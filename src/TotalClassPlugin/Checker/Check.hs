{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module TotalClassPlugin.Checker.Check ( checkConstraint ) where

import GHC.Plugins
import GHC.Tc.Types (TcM, TcGblEnv (tcg_binds))
import GHC (Class, instanceDFunId)
import GHC.ThToHs (convertToHsDecls)
import GHC.Rename.Module (findSplice)
import GHC.Tc.Module (rnTopSrcDecls, tcTopSrcDecls)
import GHC.Tc.Solver (captureTopConstraints)
import qualified GHC.Tc.Utils.Monad as TcM
import GHC.HsToCore.Monad (initDsTc)
import GHC.HsToCore.Binds (dsTopLHsBinds)
import GHC.Tc.Zonk.Type (zonkTopDecls)
import GHC.Data.Bag (emptyBag)
import GHC.Tc.Errors.Types (TcRnMessage (TcRnTHError), THError (THSpliceFailed), SpliceFailReason (..))
import TotalClassPlugin.Checker.TH (mkEvidenceFun)
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import GHC.Core.Predicate (Pred(..), classifyPredType, mkClassPred)
import GHC.Core.InstEnv (ClsInst (..), lookupInstEnv, getPotentialUnifiers, instanceBindFun)
import GHC.Tc.Utils.Env (tcGetInstEnvs, tcExtendIdEnv)
import TotalClassPlugin.Checker.Errors (checkDsResult, TotalClassCheckerMessage (..), checkTcRnResult, checkPaterson, checkQuasiError)
import TotalClassPlugin.GHCUtils (checkInstTermination, splitInstTyForValidity)
import TotalClassPlugin.Rewriter.Utils (failTcM)
import GHC.Tc.Utils.TcType (tyCoVarsOfTypesList)
import GHC.Tc.Utils.Instantiate (tcInstSkolTyVars, instDFunType)
import GHC.Tc.Types.Origin (unkSkol)
import GHC.Core.Unify (tcUnifyTysFG, UnifyResultM (..))
import GHC.Core.TyCo.Rep (Type(..))
import Data.Foldable (Foldable(toList), forM_)
import GHC.Types.Unique (getKey)
import Data.Functor.Compose (Compose(Compose, getCompose))
import Control.Monad.State (lift)
import TotalClassPlugin.Checker.CM

checkConstraint :: Class -> [Type] -> Bool -> TcM (Bool, Bool, Bool)
checkConstraint cls args fail_on_err = runCM fail_on_err (checkConstraint' cls args)

checkConstraint' :: Class -> [Type] -> CM ()
checkConstraint' cls args = do
  (vars, tys) <- lift $ inst_vars args
  results <- lift $ get_all_unifiers cls tys
  types <- mapM (check_instance cls tys vars ) results
  ev_fun <- lift $ withThTypes (Compose types) (mkEvidenceFun . getCompose)
  mb_ex_err <- either (return . Just) (lift . check_evidence_fun cls) ev_fun
  maybeFailCM Exhaustiveness mb_ex_err

inst_vars :: [Type] -> TcM ([TcTyVar], [Type])
inst_vars tys = do
  (subst, vars) <- tcInstSkolTyVars unkSkol (tyCoVarsOfTypesList tys)
  return (vars, substTys subst tys)

get_all_unifiers :: Class -> [Type] -> TcM [ClsInst]
get_all_unifiers cls tys = do
  inst_envs <- tcGetInstEnvs
  let (successful, potential, _) = lookupInstEnv False inst_envs cls tys
  return $ (fst <$> successful) ++ getPotentialUnifiers potential

check_instance :: Class -> [Type] -> [TyVar] -> ClsInst -> CM [Type]
check_instance cls tys vars inst = do
  lift (check_termination inst) >>= maybeFailCM Termination
  let res = tcUnifyTysFG instanceBindFun (is_tys inst) tys
  case res of 
    Unifiable subst_inst -> do
      let mb = map (lookupTyVar subst_inst) (is_tvs inst)   
      (_, cxt) <- lift $ instDFunType (is_dfun inst) mb
      let cxt' = substTheta subst_inst cxt
      forM_ cxt' (check_cxt_constraint cls tys inst) 
      let patterns = substTys subst_inst (TyVarTy <$> vars)
      return patterns
    MaybeApart _ _ -> lift $ failTcM $ text "bug! instance returned from lookup is MaybeApart"
    SurelyApart -> lift $ failTcM $ text "bug! instance returned from lookup is SurelyApart"

check_cxt_constraint :: Class -> [Type] -> ClsInst -> PredType -> CM ()
check_cxt_constraint cls initial_tys inst pred_ty 
  | ClassPred cls' tys <- classifyPredType pred_ty = if
    | cls' == cls -> do
      (_, tys') <- lift $ inst_vars tys
      case tcUnifyTysFG instanceBindFun initial_tys tys' of
        Unifiable _ -> return ()
        _ -> failCM Context $ TotalCheckerInvalidContext (mkClassPred cls initial_tys) pred_ty 
    | otherwise ->  failCM Context (TotalCheckerInvalidContext pred_ty (idType (instanceDFunId inst)))
  | otherwise = failCM Context TotalError

check_termination :: ClsInst -> TcM (Maybe TotalClassCheckerMessage)
check_termination = checkPaterson . TcM.tryTc . uncurry checkInstTermination . splitInstTyForValidity . idType . is_dfun

withThTypes :: Traversable t => t Type -> (t TH.Type -> TH.Q a) -> TcM (Either TotalClassCheckerMessage a)
withThTypes types thing_inside = do
  ty_ids <- mapM (TcM.newSysLocalId (fsLit "temp") OneTy) types
  tcExtendIdEnv (toList ty_ids) $ checkQuasiError $ do
    th_types <- mapM (TH.reifyType . TH.mkNameU "temp" . toInteger . getKey . idUnique) ty_ids
    thing_inside th_types

check_evidence_fun :: Class -> [TH.Dec] -> TcM (Maybe TotalClassCheckerMessage)
check_evidence_fun cls decs = do
  binds <- checkTcRnResult $ TcM.tryTc $ do
    ev_fun_binds <- case convertToHsDecls (Generated DoPmc) noSrcSpan decs of
      Left err -> TcM.failWithTc $ TcRnTHError (THSpliceFailed (RunSpliceFailure err))
      Right ev_fun_binds -> return ev_fun_binds
    (group, Nothing) <- findSplice ev_fun_binds
    (gbl_rn, rn_group) <- TcM.updGblEnv (\env -> env{tcg_binds=emptyBag}) $ rnTopSrcDecls group
    ((gbl_tc, _), _) <- captureTopConstraints $ TcM.setGblEnv gbl_rn $ tcTopSrcDecls rn_group
    (_, _, binds, _, _, _) <- TcM.setGblEnv gbl_tc $ zonkTopDecls emptyBag (tcg_binds gbl_tc) [] [] [] 
    return binds
  checkDsResult cls $ TcM.updTopFlags (flip wopt_set Opt_WarnIncompletePatterns) $ initDsTc $ dsTopLHsBinds binds
