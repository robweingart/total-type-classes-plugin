{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

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
  ClassPred targetClass [c] -> do
    checkClass <- getCheckClass
    checkResultClass <- getCheckResultClass
    if | targetClass == checkClass ->       check_inner ct c True
       | targetClass == checkResultClass -> check_inner ct c False
       | otherwise -> return Nothing
  _ -> do
    return Nothing

check_inner :: Ct -> PredType -> Bool -> TcPluginM (Maybe (EvTerm, Ct))
check_inner ct c fail_on_err = case classifyPredType c of
  ForAllPred _ _ inner -> check_inner ct inner fail_on_err
  ClassPred cls args -> do
    res <- unsafeTcPluginTcM (setCtLocM (ctLoc ct) $ checkConstraint cls args fail_on_err)
    ev_term <- if fail_on_err
      then mk_check_inst c
      else mk_check_result_inst c res
    return $ Just (ev_term, ct)
  _ -> return Nothing

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

