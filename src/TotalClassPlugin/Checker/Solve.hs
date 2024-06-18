{-# LANGUAGE MultiWayIf #-}

module TotalClassPlugin.Checker.Solve ( solveCheck ) where

import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types.Evidence (EvTerm (EvExpr))
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc)
import GHC.Tc.Types (TcM, TcGblEnv (tcg_binds))
import GHC (Class)
import Data.Maybe (mapMaybe, maybeToList)
import GHC.Core.Class (Class(classTyCon, className))
import GHC.ThToHs (convertToHsDecls)
import GHC.Rename.Module (findSplice)
import GHC.Tc.Module (rnTopSrcDecls, tcTopSrcDecls)
import GHC.Tc.Solver (captureTopConstraints)
import GHC.Tc.Utils.Monad (setGblEnv, updTopFlags, updGblEnv, failWithTc, setCtLocM, tryTc, mapAndUnzipM)
import GHC.HsToCore.Monad (initDsTc)
import GHC.HsToCore.Binds (dsTopLHsBinds)
import GHC.Tc.Zonk.Type (zonkTopDecls)
import GHC.Data.Bag (emptyBag)
import GHC.Tc.Errors.Types (TcRnMessage (TcRnTHError), THError (THSpliceFailed), SpliceFailReason (..))
import TotalClassPlugin.Checker.TH (mkEvidenceFun)
import Language.Haskell.TH (mkName)
import GHC.Core.Predicate (Pred(..), classifyPredType)
import GHC.Core.InstEnv (classInstances, ClsInst (is_dfun))
import GHC.Tc.Utils.Env (tcGetInstEnvs)
import TotalClassPlugin.Checker.Errors (checkDsResult, TotalClassCheckerMessage (TotalCheckerInvalidContext), checkTcRnResult, failWithTotal, checkPaterson, checkQuasiError)
import GHC.Data.Maybe (listToMaybe)
import TotalClassPlugin.GHCUtils (checkInstTermination, splitInstTyForValidity)

getCheckClass :: TcPluginM Class
getCheckClass = do
  Found _ md <- findImportedModule (mkModuleName "TotalClassPlugin") NoPkgQual
  name <- lookupOrig md (mkClsOcc "CheckTotality")
  tcLookupClass name

getCheckResultClass :: TcPluginM Class
getCheckResultClass = do
  Found _ md <- findImportedModule (mkModuleName "TotalClassPlugin") NoPkgQual
  name <- lookupOrig md (mkClsOcc "CheckTotalityResult")
  tcLookupClass name

getTotalityEvidenceType :: TcPluginM TyCon
getTotalityEvidenceType = do
  Found _ md <- findImportedModule (mkModuleName "TotalClassPlugin") NoPkgQual
  name <- lookupOrig md (mkTcOcc "TotalityEvidence")
  tcLookupTyCon name

solveCheck :: Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveCheck ct = case classifyPredType (ctPred ct) of
  ClassPred targetClass tys -> do
    tcPluginIO $ putStrLn "checking for CheckTotality"
    checkClass <- getCheckClass
    checkResultClass <- getCheckResultClass
    let maybe_get_result = if | targetClass == checkClass -> Just False
                              | targetClass == checkResultClass -> Just True
                              | otherwise -> Nothing
    case maybe_get_result of
      Nothing -> return Nothing
      Just get_result -> case tys of
        [ck, c] | ClassPred cls [] <- classifyPredType c  -> do
            res <- unsafeTcPluginTcM (setCtLocM (ctLoc ct) $ check cls (not get_result))
            ev_term <- if get_result
              then mk_check_result_inst ck cls res
              else mk_check_inst ck cls
            return $ Just (ev_term, ct)
        _ -> fail "wrong class app type"
  _ -> return Nothing

check :: Class -> Bool -> TcM (Bool, Bool, Bool)
check cls fail_on_err = do
  maybe_ex_msg <- check_exhaustiveness cls
  ex_res <- res_or_fail maybe_ex_msg
  inst_envs <- tcGetInstEnvs
  (term_msgss, ctxt_msgss) <- mapAndUnzipM check_inst (classInstances inst_envs cls)
  term_res <- res_or_fail (listToMaybe (concat term_msgss))
  ctxt_res <- res_or_fail (listToMaybe (concat ctxt_msgss))
  return (ex_res, term_res, ctxt_res)
  where
    res_or_fail (Just m) = if fail_on_err then failWithTotal m else return False
    res_or_fail Nothing = return True

    check_inst inst = do
      let dfun_type = idType $ is_dfun inst
      let (theta, tau) = splitInstTyForValidity dfun_type
      term_res <- checkPaterson $ tryTc $ checkInstTermination theta tau
      let ctxt_res = check_context theta tau
      return (maybeToList term_res, ctxt_res)

    check_pred_type tau pred_ty = case classifyPredType pred_ty of
      ClassPred cls' _ | cls == cls' -> Nothing
      _ -> Just (TotalCheckerInvalidContext pred_ty tau)

    check_context theta tau = mapMaybe (check_pred_type tau) theta


check_exhaustiveness :: Class -> TcM (Maybe TotalClassCheckerMessage)
check_exhaustiveness cls = do
  let name = mkName $ occNameString $ nameOccName $ className cls
  --let match_on = mapMaybe match_on_bndr $ tyConBinders (classTyCon cls)
  let arity = length $ tyConBinders (classTyCon cls)
  th_res <- checkQuasiError (mkEvidenceFun name arity)
  case th_res of
    Left err -> return (Just err)
    Right ev_fun_dec -> do
      binds <- checkTcRnResult $ tryTc $ do
        ev_fun_binds <- case convertToHsDecls (Generated DoPmc) noSrcSpan ev_fun_dec of
          Left err -> failWithTc $ TcRnTHError (THSpliceFailed (RunSpliceFailure err))
          Right ev_fun_binds -> return ev_fun_binds
        (group, Nothing) <- findSplice ev_fun_binds
        (gbl_rn, rn_group) <- updGblEnv (\env -> env{tcg_binds=emptyBag}) $ rnTopSrcDecls group
        ((gbl_tc, _), _) <- captureTopConstraints $ setGblEnv gbl_rn $ tcTopSrcDecls rn_group
        (_, _, binds, _, _, _) <- setGblEnv gbl_tc $ zonkTopDecls emptyBag (tcg_binds gbl_tc) [] [] [] 
        return binds
      checkDsResult cls $ updTopFlags (flip wopt_set Opt_WarnIncompletePatterns) $ initDsTc $ dsTopLHsBinds binds
  --where
  --  match_on_bndr (Bndr _ (NamedTCB _)) = Nothing
  --  match_on_bndr (Bndr var AnonTCB) = Just $ isAlgType (tyVarKind var)


mk_check_inst :: Type -> Class -> TcPluginM EvTerm
mk_check_inst ck cls = do
  check_class <- getCheckClass
  tot_ev_tc <- getTotalityEvidenceType
  let c_ty = mkTyConTy (classTyCon cls)
  let tot_ev_ty = mkTyConApp tot_ev_tc [ck, c_ty]
  let check_dc = tyConSingleDataCon (classTyCon check_class)
  return $ EvExpr $ mkCoreConApps check_dc [Type ck, Type c_ty, mkImpossibleExpr tot_ev_ty "TotalityEvidence"]

mk_check_result_inst :: Type -> Class -> (Bool, Bool, Bool) -> TcPluginM EvTerm
mk_check_result_inst ck cls (ex_res, term_res, ctxt_res) = do
  check_result_class <- getCheckResultClass
  let c_ty = mkTyConTy (classTyCon cls)
  let check_result_dc = tyConSingleDataCon (classTyCon check_result_class)
  return $ EvExpr $ mkCoreConApps check_result_dc [Type ck, Type c_ty, boolToCoreExpr ex_res, boolToCoreExpr term_res, boolToCoreExpr ctxt_res]

boolToCoreExpr :: Bool -> CoreExpr
boolToCoreExpr False = mkConApp falseDataCon []
boolToCoreExpr True = mkConApp trueDataCon []

