{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module TotalClassPlugin.Checker.Check (checkConstraint) where

import Control.Monad (filterM, unless)
import Data.Foldable (Foldable (toList))
import Data.Functor.Compose (Compose (Compose, getCompose))
import Data.Maybe (isJust)
import GHC (Class)
import GHC.Core.InstEnv (ClsInst (..), getPotentialUnifiers, instanceBindFun, lookupInstEnv, instanceHead)
import GHC.Core.Predicate (Pred (ClassPred), classifyPredType, mkClassPred)
import GHC.Core.TyCo.Rep (Type (..))
import GHC.Core.Unify (UnifyResultM (..), tcMatchTys, tcUnifyTysFG)
import GHC.Data.Bag (emptyBag, headMaybe)
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
import GHC.Tc.Utils.Unify (buildImplicationFor)
import GHC.Tc.Zonk.Type (zonkTopDecls)
import GHC.ThToHs (convertToHsDecls)
import GHC.Types.Unique (getKey)
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import TotalClassPlugin.Checker.CM
import TotalClassPlugin.Checker.Errors (checkDsResult, checkQuasiError, checkTcRnResult, TotalFailureDetails (..))
import TotalClassPlugin.Checker.TH (mkEvidenceFun)
import TotalClassPlugin.Rewriter.Utils (failTcM)
import GHC.Tc.Utils.TcType (ltPatersonSize, pSizeClassPred, mkSpecSigmaTy, PatersonSize, pSizeType)
import GHC.Tc.Errors (reportUnsolved)
import GHC.Types.Error (Messages(getMessages), MsgEnvelope (errMsgDiagnostic, MsgEnvelope))

checkConstraint :: [TyVar] -> [PredType] -> Class -> [Type] -> Bool -> TcM (Bool, Bool, Bool)
checkConstraint tvs givens cls args fail_on_err = runCM fail_on_err (mkSpecSigmaTy tvs [] (mkClassPred cls args)) (checkConstraint' tvs givens cls args)

checkConstraint' :: [TyVar] -> [PredType] -> Class -> [Type] -> CM ()
checkConstraint' tvs givens cls args = do
  (subst, vars) <- liftTcM $ tcInstSkolTyVars unkSkol tvs
  givens' <- liftTcM $ newEvVars (substTys subst givens)
  let tys = substTys subst args
  results <- liftTcM $ get_all_unifiers cls tys
  types <- mapM (check_instance givens' cls tys vars) results
  ev_fun <- withThTypes (Compose types) (mkEvidenceFun . getCompose)
  mb_ex_err <- either (return . Just) (check_evidence_fun cls) ev_fun
  maybeFailCM Exhaustiveness mb_ex_err

get_all_unifiers :: Class -> [Type] -> TcM [ClsInst]
get_all_unifiers cls tys = do
  inst_envs <- tcGetInstEnvs
  let (successful, potential, _) = lookupInstEnv False inst_envs cls tys
  return $ (fst <$> successful) ++ getPotentialUnifiers potential

check_instance :: [EvVar] -> Class -> [Type] -> [TcTyVar] -> ClsInst -> CM [Type]
check_instance givens cls tys vars inst = do
  let res = tcUnifyTysFG instanceBindFun (is_tys inst) tys
  case res of
    Unifiable subst_inst -> do
      let mb = map (lookupTyVar subst_inst) (is_tvs inst)
      let (_, _, head_tys) = instanceHead inst
      let head_psize = pSizeType (mkClassPred cls (substTys subst_inst head_tys))
      (_, cxt) <- liftTcM $ instDFunType (is_dfun inst) mb
      remaining <- filterM (fmap not . can_solve_recursively cls tys head_psize) $ substTheta subst_inst cxt
      case remaining of
        [] -> return ()
        _ -> do
          tc_level <- liftTcM $ getLclEnvTcLevel <$> getLclEnv
          wanteds <- liftTcM $ newWanteds (GivenOrigin (UnkSkol emptyCallStack)) remaining
          (implications, _) <- liftTcM $ buildImplicationFor tc_level (UnkSkol emptyCallStack) vars givens (mkSimpleWC wanteds)
          (wcs, _) <- liftTcM $ runTcS $ solveWanteds (mkImplicWC implications)
          unless (isSolvedWC wcs) $ do
            (_, msgs) <- liftTcM $ TcM.tryTc $ reportUnsolved wcs
            case headMaybe (getMessages msgs) of
              Nothing -> liftTcM $ failTcM $ text "failed to solve constraints from context, but no errors"
              Just (MsgEnvelope{errMsgDiagnostic=err}) -> failCM Context (TotalContextNotSolved (mkClassPred cls tys) err)
      let patterns = substTys subst_inst (TyVarTy <$> vars)
      return patterns
    MaybeApart _ _ -> liftTcM $ failTcM $ text "bug! instance returned from lookup is MaybeApart"
    SurelyApart -> liftTcM $ failTcM $ text "bug! instance returned from lookup is SurelyApart"

can_solve_recursively :: Class -> [Type] -> PatersonSize -> PredType -> CM Bool
can_solve_recursively cls tys inst_head_psize pred_ty
  | ClassPred cls' tys' <- classifyPredType pred_ty,
    cls == cls' = do
      unless (isJust (tcMatchTys tys tys')) $ failCM Context (TotalContextEscapes {tcc_msg_inst_head = mkClassPred cls tys, tcc_msg_wanted = pred_ty})
      case (pSizeClassPred cls' tys' `ltPatersonSize` inst_head_psize) of
        Nothing -> return ()
        Just pcf -> failCM Termination (TotalContextNotSmaller  {tcc_msg_inst_head = mkClassPred cls tys, tcc_msg_wanted = pred_ty, tcc_msg_paterson_pcf = pcf})
      return True
  | otherwise = return False

withThTypes :: (Traversable t) => t Type -> (t TH.Type -> TH.Q a) -> CM (Either TotalFailureDetails a)
withThTypes types thing_inside = do
  ty_ids <- liftTcM $ mapM (TcM.newSysLocalId (fsLit "temp") OneTy) types
  original <- getOriginalConstraint
  liftTcM $ tcExtendIdEnv (toList ty_ids) $ checkQuasiError original $ do
    th_types <- mapM (TH.reifyType . TH.mkNameU "temp" . toInteger . getKey . idUnique) ty_ids
    thing_inside th_types

check_evidence_fun :: Class -> [TH.Dec] -> CM (Maybe TotalFailureDetails)
check_evidence_fun cls decs = do
  original <- getOriginalConstraint
  tc_rn_result <- liftTcM $ checkTcRnResult original $ TcM.tryTc $ TcM.updTopFlags (flip wopt_unset Opt_WarnUnusedMatches) $ do
    ev_fun_binds <- case convertToHsDecls (Generated DoPmc) noSrcSpan decs of
      Left err -> TcM.failWithTc $ TcRnTHError (THSpliceFailed (RunSpliceFailure err))
      Right ev_fun_binds -> return ev_fun_binds
    (group, Nothing) <- findSplice ev_fun_binds
    (gbl_rn, rn_group) <- TcM.updGblEnv (\env -> env {tcg_binds = emptyBag}) $ rnTopSrcDecls group
    ((gbl_tc, _), _) <- captureTopConstraints $ TcM.setGblEnv gbl_rn $ tcTopSrcDecls rn_group
    (_, _, binds, _, _, _) <- TcM.setGblEnv gbl_tc $ zonkTopDecls emptyBag (tcg_binds gbl_tc) [] [] []
    return binds
  case tc_rn_result of
    Left err -> return $ Just err
    Right binds -> liftTcM $
                   checkDsResult original cls $ TcM.updTopFlags (flip wopt_set Opt_WarnIncompletePatterns) $ initDsTc $ dsTopLHsBinds binds
