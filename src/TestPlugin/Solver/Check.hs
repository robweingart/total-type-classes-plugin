module TestPlugin.Solver.Check where

import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types.Evidence (EvTerm (EvExpr))
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc)
import GHC.Tc.Types (TcM, TcGblEnv (tcg_binds), TcLclEnv (tcl_errs))
import GHC (Class, emptyRdrGroup, HsGroup (hs_valds), HsMatchContext (FunRhs, mc_fun))
import Language.Haskell.TH (mkName, runQ, nameSpace)
import Language.Haskell.TH.Syntax (lift)
import Data.Maybe (mapMaybe)
import GHC.Core.Class (Class(classTyCon, className))
import TestPlugin (CheckerResult (NotExhaustive, CheckerSuccess))
import GHC.Tc.Gen.Splice (runQuasi)
import GHC.ThToHs (convertToHsDecls)
import GHC.Tc.Types.Origin (UserTypeCtxt(GenSigCtxt))
import GHC.Tc.Gen.Bind (tcTopBinds)
import GHC.Rename.Bind (rnTopBindsLHS, makeMiniFixityEnv)
import GHC.Rename.Module (findSplice)
import GHC.Tc.Module (rnTopSrcDecls, tcTopSrcDecls)
import GHC.Tc.Solver (captureTopConstraints)
import TestPlugin.Rewriter.Utils (outputTcM)
import GHC.Tc.Utils.Monad (readTcRef, setGblEnv, updTopEnv, updTopFlags, updGblEnv, addDiagnosticTcM, addErrTc, failWithTc, setCtLocM)
import GHC.HsToCore.Monad (initDsTc)
import GHC.HsToCore.Binds (dsTopLHsBinds)
import GHC.Tc.Zonk.Type (zonkTopDecls)
import GHC.Data.Bag (emptyBag, filterBag, mapMaybeBag, headMaybe)
import GHC.Data.EnumSet (insert)
import GHC.Types.Error (MsgEnvelope(MsgEnvelope, errMsgDiagnostic), Messages (getMessages))
import GHC.HsToCore.Errors.Types (DsMessage(DsNonExhaustivePatterns))
import GHC.Tc.Errors.Types (mkTcRnUnknownMessage)
import Control.Monad (when)
import GHC.Plugins (tidyNameOcc, occNameString, nameOccName)
import TestPlugin.Solver.TH (mkEvidenceFun)

getCheckClass :: TcPluginM Class
getCheckClass = do
  Found _ md <- findImportedModule (mkModuleName "TestPlugin") NoPkgQual
  name <- lookupOrig md (mkClsOcc "CheckTotality")
  tcLookupClass name

getTotalityEvidenceType :: TcPluginM TyCon
getTotalityEvidenceType = do
  Found _ md <- findImportedModule (mkModuleName "TestPlugin") NoPkgQual
  name <- lookupOrig md (mkTcOcc "TotalityEvidence")
  tcLookupTyCon name

addErrDsTc :: DsMessage -> TcM ()
addErrDsTc ds_msg = addErrTc (mkTcRnUnknownMessage ds_msg)

failWithDsTc :: DsMessage -> TcM a
failWithDsTc ds_msg = failWithTc (mkTcRnUnknownMessage ds_msg)

solveCheck :: Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveCheck ct = case splitTyConApp_maybe (ctPred ct) of
  Just (tc, tys) | Just targetClass <- tyConClass_maybe tc -> do
    tcPluginIO $ putStrLn "checking for CheckTotality"
    checkClass <- getCheckClass
    if targetClass /= checkClass
    then return Nothing
    else case tys of
      --[ck, c, opt] | Just (opt_tc, opt_tys) <- splitTyConApp_maybe opt -> case opt_tys of
      --  [ex_opt, term_opt] -> do
      --    do_ex <- case splitTyConApp_maybe of
      --      Just ex_opt_tc -> 
      --  _ -> fail "wrong options type"
      [ck, c] -> case splitTyConApp_maybe c of
        Just (tc', []) | Just cls <- tyConClass_maybe tc' -> do
          CheckerSuccess <- unsafeTcPluginTcM (setCtLocM (ctLoc ct) $ check cls True)
          ev_term <- mk_check_inst ck tc'
          return $ Just (ev_term, ct)
            
        _ -> return Nothing
        
        
      _ -> fail "wrong class app type"
  _ -> return Nothing

check :: Class -> Bool -> TcM CheckerResult
check cls fail_on_err = do
  maybe_ex_msg <- check_exhaustiveness cls
  case (maybe_ex_msg, fail_on_err)  of
    (Just ex_msg, True) -> failWithDsTc ex_msg
    (Just ex_msg, False) -> addErrDsTc ex_msg >> return NotExhaustive
    (Nothing, _) -> do
      outputTcM "Internal?: " $ isInternalName (className cls)
      return CheckerSuccess
      
check_exhaustiveness :: Class -> TcM (Maybe DsMessage)
check_exhaustiveness cls = do
  let name = mkName $ occNameString $ nameOccName $ className cls
  let match_on = mapMaybe match_on_bndr $ tyConBinders (classTyCon cls)
  ev_fun_dec <- runQuasi (mkEvidenceFun name match_on)
  liftIO $ print ev_fun_dec
  case convertToHsDecls (Generated DoPmc) noSrcSpan ev_fun_dec of
    Left _err -> fail "conversion failed"
    Right ev_fun_binds -> do
      liftIO $ putStrLn $ showPprUnsafe ev_fun_binds
      (group, Nothing) <- findSplice ev_fun_binds
      (gbl_rn, rn_group) <- updGblEnv (\env -> env{tcg_binds=emptyBag}) $ rnTopSrcDecls group
      ((gbl_tc, _), _) <- captureTopConstraints $ setGblEnv gbl_rn $ tcTopSrcDecls rn_group
      outputTcM "New global env: " (tcg_binds gbl_tc)
      (_, _, binds, _, _, _) <- setGblEnv gbl_tc $ zonkTopDecls emptyBag (tcg_binds gbl_tc) [] [] [] 
      (msgs, _) <- updTopFlags (flip wopt_set Opt_WarnIncompletePatterns) $ initDsTc $ dsTopLHsBinds binds
      outputTcM "Messages: " msgs
      let non_exhaustive_msgs = mapMaybeBag get_non_exhaustive_msg $ getMessages msgs
      return $ headMaybe non_exhaustive_msgs
  where
    match_on_bndr (Bndr _ (NamedTCB _)) = Nothing
    match_on_bndr (Bndr var AnonTCB) = Just $ isAlgType (tyVarKind var)

    get_non_exhaustive_msg (MsgEnvelope{errMsgDiagnostic=(DsNonExhaustivePatterns cxt@FunRhs{mc_fun=(L l name)} flag maxPatterns vars nablas)}) = Just ds_msg
      where
        occ_name = mkOccName (nameNameSpace name) $ "the exhaustiveness check for " ++ (occNameString $ nameOccName $ className cls)
        new_name = tidyNameOcc name occ_name
        ds_msg = DsNonExhaustivePatterns (cxt{mc_fun=(L l new_name)}) flag maxPatterns vars nablas
    get_non_exhaustive_msg _ = Nothing

mk_check_inst :: Type -> TyCon -> TcPluginM EvTerm
mk_check_inst ck tc = do
  check_class <- getCheckClass
  tot_ev_tc <- getTotalityEvidenceType
  let c_ty = mkTyConTy tc
  let tot_ev_ty = mkTyConApp tot_ev_tc [ck, c_ty]
  let check_dc = tyConSingleDataCon (classTyCon check_class)
  return $ EvExpr $ mkCoreConApps check_dc [Type ck, Type c_ty, mkImpossibleExpr tot_ev_ty "TotalityEvidence"]

