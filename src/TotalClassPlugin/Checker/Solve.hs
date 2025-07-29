{-# LANGUAGE MultiWayIf #-}

module TotalClassPlugin.Checker.Solve ( solveCheck ) where

import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types.Evidence (EvTerm (EvExpr))
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc)
import GHC (Class)
import GHC.Tc.Utils.Monad (setCtLocM)
import GHC.Core.Predicate (Pred(..), classifyPredType)
import GHC.Core.Class (classTyCon)
import TotalClassPlugin.Checker.Check
import GHC.Tc.Utils.TcType (tyCoVarsOfTypeList)

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

solveCheck :: [Ct] -> Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveCheck givens ct = case classifyPredType (ctPred ct) of
  ClassPred targetClass [c] -> do
    checkClass <- getCheckClass
    checkResultClass <- getCheckResultClass
    if | targetClass == checkClass ->       check_inner givens ct c True
       | targetClass == checkResultClass -> check_inner givens ct c False
       | otherwise -> return Nothing
  _ -> do
    return Nothing

check_inner :: [Ct] -> Ct -> PredType -> Bool -> TcPluginM (Maybe (EvTerm, Ct))
check_inner given_cts ct c fail_on_err = go free_vars (map ctPred given_cts) (classifyPredType c)
  where
    free_vars = tyCoVarsOfTypeList c

    go tvs givens (ForAllPred tvs' givens' inner) = go (tvs ++ tvs') (givens ++ givens') (classifyPredType inner)
    go tvs givens (ClassPred cls args) = do
      res <- unsafeTcPluginTcM (setCtLocM (ctLoc ct) $ checkConstraint tvs givens cls args fail_on_err)
      ev_term <- if fail_on_err
        then mk_check_inst c
        else mk_check_result_inst c res
      return $ Just (ev_term, ct)
    go _ _ _ = return Nothing

mk_check_inst :: PredType -> TcPluginM EvTerm
mk_check_inst c = do
  check_class <- getCheckClass
  tot_ev_tc <- getTotalityEvidenceType
  let tot_ev_ty = mkTyConApp tot_ev_tc [c]
  let check_dc = tyConSingleDataCon (classTyCon check_class)
  return $ EvExpr $ mkCoreConApps check_dc [Type c, mkImpossibleExpr tot_ev_ty "TotalityEvidence"]

mk_check_result_inst :: PredType -> (Bool, Bool, Bool) -> TcPluginM EvTerm
mk_check_result_inst c (ex_res, term_res, ctxt_res) = do
  check_result_class <- getCheckResultClass
  let check_result_dc = tyConSingleDataCon (classTyCon check_result_class)
  return $ EvExpr $ mkCoreConApps check_result_dc [Type c, boolToCoreExpr ex_res, boolToCoreExpr term_res, boolToCoreExpr ctxt_res]

boolToCoreExpr :: Bool -> CoreExpr
boolToCoreExpr False = mkConApp falseDataCon []
boolToCoreExpr True = mkConApp trueDataCon []

