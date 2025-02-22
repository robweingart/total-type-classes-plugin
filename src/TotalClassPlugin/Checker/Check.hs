{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module TotalClassPlugin.Checker.Check (checkConstraint) where

import Control.Monad (unless)
import Control.Monad.State (lift)
import Data.Foldable (Foldable (toList))
import Data.Functor.Compose (Compose (Compose, getCompose))
import GHC (Class, instanceDFunId)
import GHC.Core.InstEnv (ClsInst (..), getPotentialUnifiers, instanceBindFun, lookupInstEnv)
import GHC.Core.Predicate (mkClassPred)
import GHC.Core.TyCo.Rep (Type (..))
import GHC.Core.Unify (UnifyResultM (..), tcUnifyTysFG)
import GHC.Data.Bag (emptyBag)
import GHC.HsToCore.Binds (dsTopLHsBinds)
import GHC.HsToCore.Monad (initDsTc)
import GHC.Plugins
import GHC.Rename.Module (findSplice)
import GHC.Stack (emptyCallStack)
import GHC.Tc.Errors.Types (SpliceFailReason (..), THError (THSpliceFailed), TcRnMessage (TcRnTHError))
import GHC.Tc.Module (rnTopSrcDecls, tcTopSrcDecls)
import GHC.Tc.Solver (captureTopConstraints, solveWanteds)
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Types (TcGblEnv (tcg_binds), TcM, getLclEnvTcLevel)
import GHC.Tc.Types.Constraint (isSolvedWC, mkImplicWC, mkSimpleWC)
import GHC.Tc.Types.Origin (CtOrigin (..), SkolemInfoAnon (UnkSkol), unkSkol)
import GHC.Tc.Utils.Env (tcExtendIdEnv, tcGetInstEnvs)
import GHC.Tc.Utils.Instantiate (instDFunType, newWanteds, tcInstSkolTyVars)
import GHC.Tc.Utils.Monad (getLclEnv)
import qualified GHC.Tc.Utils.Monad as TcM
import GHC.Tc.Utils.TcMType (newEvVars)
import GHC.Tc.Utils.TcType (mkSpecSigmaTy)
import GHC.Tc.Utils.Unify (buildImplicationFor)
import GHC.Tc.Zonk.Type (zonkTopDecls)
import GHC.ThToHs (convertToHsDecls)
import GHC.Types.Unique (getKey)
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import TotalClassPlugin.Checker.CM
import TotalClassPlugin.Checker.Errors (TotalClassCheckerMessage (..), checkDsResult, checkPaterson, checkQuasiError, checkTcRnResult)
import TotalClassPlugin.Checker.TH (mkEvidenceFun)
import TotalClassPlugin.GHCUtils (checkInstTermination, splitInstTyForValidity)
import TotalClassPlugin.Rewriter.Utils (failTcM)

checkConstraint :: [TyVar] -> Class -> [Type] -> Bool -> TcM (Bool, Bool, Bool)
checkConstraint tvs cls args fail_on_err = runCM fail_on_err (checkConstraint' tvs cls args)

checkConstraint' :: [TyVar] -> Class -> [Type] -> CM ()
checkConstraint' tvs cls args = do
  let original = mkSpecSigmaTy tvs [] (mkClassPred cls args)
  (subst, vars) <- lift $ tcInstSkolTyVars unkSkol tvs
  let tys = substTys subst args
  results <- lift $ get_all_unifiers cls tys
  types <- mapM (check_instance original cls tys vars) results
  ev_fun <- lift $ withThTypes (Compose types) (mkEvidenceFun . getCompose)
  mb_ex_err <- either (return . Just) (lift . check_evidence_fun cls) ev_fun
  maybeFailCM Exhaustiveness mb_ex_err

get_all_unifiers :: Class -> [Type] -> TcM [ClsInst]
get_all_unifiers cls tys = do
  inst_envs <- tcGetInstEnvs
  let (successful, potential, _) = lookupInstEnv False inst_envs cls tys
  return $ (fst <$> successful) ++ getPotentialUnifiers potential

check_instance :: Type -> Class -> [Type] -> [TcTyVar] -> ClsInst -> CM [Type]
check_instance original cls tys vars inst = do
  lift (check_termination inst) >>= maybeFailCM Termination
  let res = tcUnifyTysFG instanceBindFun (is_tys inst) tys
  case res of
    Unifiable subst_inst -> do
      let mb = map (lookupTyVar subst_inst) (is_tvs inst)
      (_, cxt) <- lift $ instDFunType (is_dfun inst) mb
      let cxt' = substTheta subst_inst cxt
      case cxt' of
        [] -> return ()
        _ -> do
          tc_level <- lift $ getLclEnvTcLevel <$> getLclEnv
          wanteds <- lift $ newWanteds (GivenOrigin (UnkSkol emptyCallStack)) cxt'
          givens <- lift $ newEvVars [original]
          (implications, _) <- lift $ buildImplicationFor tc_level (UnkSkol emptyCallStack) vars givens (mkSimpleWC wanteds)
          (wcs, _) <- lift $ runTcS $ solveWanteds (mkImplicWC implications)
          unless (isSolvedWC wcs) $ do
            failCM Context (TotalCheckerInvalidContext (mkClassPred cls tys))
      let patterns = substTys subst_inst (TyVarTy <$> vars)
      return patterns
    MaybeApart _ _ -> lift $ failTcM $ text "bug! instance returned from lookup is MaybeApart"
    SurelyApart -> lift $ failTcM $ text "bug! instance returned from lookup is SurelyApart"

check_termination :: ClsInst -> TcM (Maybe TotalClassCheckerMessage)
check_termination = checkPaterson . TcM.tryTc . uncurry checkInstTermination . splitInstTyForValidity . idType . is_dfun

withThTypes :: (Traversable t) => t Type -> (t TH.Type -> TH.Q a) -> TcM (Either TotalClassCheckerMessage a)
withThTypes types thing_inside = do
  ty_ids <- mapM (TcM.newSysLocalId (fsLit "temp") OneTy) types
  tcExtendIdEnv (toList ty_ids) $ checkQuasiError $ do
    th_types <- mapM (TH.reifyType . TH.mkNameU "temp" . toInteger . getKey . idUnique) ty_ids
    thing_inside th_types

check_evidence_fun :: Class -> [TH.Dec] -> TcM (Maybe TotalClassCheckerMessage)
check_evidence_fun cls decs = do
  tc_rn_result <- checkTcRnResult $ TcM.tryTc $ TcM.updTopFlags (flip wopt_unset Opt_WarnUnusedMatches) $ do
    ev_fun_binds <- case convertToHsDecls (Generated DoPmc) noSrcSpan decs of
      Left err -> TcM.failWithTc $ TcRnTHError (THSpliceFailed (RunSpliceFailure err))
      Right ev_fun_binds -> return ev_fun_binds
    (group, Nothing) <- findSplice ev_fun_binds
    (gbl_rn, rn_group) <- TcM.updGblEnv (\env -> env {tcg_binds = emptyBag}) $ rnTopSrcDecls group
    -- outputTcM "evidence fun:" rn_group
    ((gbl_tc, _), _) <- captureTopConstraints $ TcM.setGblEnv gbl_rn $ tcTopSrcDecls rn_group
    (_, _, binds, _, _, _) <- TcM.setGblEnv gbl_tc $ zonkTopDecls emptyBag (tcg_binds gbl_tc) [] [] []
    return binds
  case tc_rn_result of
    Left err -> return $ Just err
    Right binds -> checkDsResult cls $ TcM.updTopFlags (flip wopt_set Opt_WarnIncompletePatterns) $ initDsTc $ dsTopLHsBinds binds
