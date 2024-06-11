{-# LANGUAGE MultiWayIf #-}

module TotalClassPlugin.Checker.Solve ( solveCheck ) where

import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types.Evidence (EvTerm (EvExpr))
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc)
import GHC.Tc.Types (TcM, TcGblEnv (tcg_binds))
import GHC (Class, HsMatchContext (FunRhs, mc_fun))
import Data.Maybe (mapMaybe)
import GHC.Core.Class (Class(classTyCon, className))
import GHC.Tc.Gen.Splice (runQuasi)
import GHC.ThToHs (convertToHsDecls)
import GHC.Rename.Module (findSplice)
import GHC.Tc.Module (rnTopSrcDecls, tcTopSrcDecls)
import GHC.Tc.Solver (captureTopConstraints)
import GHC.Tc.Utils.Monad (setGblEnv, updTopFlags, updGblEnv, addErrTc, failWithTc, setCtLocM, tryTc, mapMaybeM)
import GHC.HsToCore.Monad (initDsTc)
import GHC.HsToCore.Binds (dsTopLHsBinds)
import GHC.Tc.Zonk.Type (zonkTopDecls)
import GHC.Data.Bag (emptyBag, mapMaybeBag, headMaybe)
import GHC.Types.Error (MsgEnvelope(MsgEnvelope, errMsgDiagnostic), Messages (getMessages))
import GHC.HsToCore.Errors.Types (DsMessage(DsNonExhaustivePatterns))
import GHC.Tc.Errors.Types (mkTcRnUnknownMessage, TcRnMessage (TcRnPatersonCondFailure, TcRnTHError), THError (THSpliceFailed), SpliceFailReason (..))
import TotalClassPlugin.Checker.TH (mkEvidenceFun)
import Language.Haskell.TH (mkName)
import GHC.Core.TyCo.Rep (Type(ForAllTy, FunTy, ft_af, ft_arg, ft_res))
import GHC.Tc.Utils.TcType (TcPredType, pSizeType, pSizeClassPredX, pSizeTypeX, ltPatersonSize, PatersonCondFailureContext (InInstanceDecl))
import GHC.Core.Predicate (Pred(..), classifyPredType, isCTupleClass)
import GHC.Core.InstEnv (classInstances, ClsInst (is_dfun))
import Data.Foldable (forM_)
import GHC.Tc.Utils.Env (tcGetInstEnvs)
import TotalClassPlugin.Checker.Errors (checkDsResult, TotalClassCheckerMessage, checkTcRnResult, failWithTotal, checkPaterson)
import GHC.Data.Maybe (listToMaybe)
import Data.Bool (bool)

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
solveCheck ct = case splitTyConApp_maybe (ctPred ct) of
  Just (tc, tys) | Just targetClass <- tyConClass_maybe tc -> do
    tcPluginIO $ putStrLn "checking for CheckTotality"
    checkClass <- getCheckClass
    checkResultClass <- getCheckResultClass
    let maybe_get_result = if | targetClass == checkClass -> Just False
                              | targetClass == checkResultClass -> Just True
                              | otherwise -> Nothing
    case maybe_get_result of
      Nothing -> return Nothing
      Just get_result -> case tys of
        --[ck, c, opt] | Just (opt_tc, opt_tys) <- splitTyConApp_maybe opt -> case opt_tys of
        --  [ex_opt, term_opt] -> do
        --    do_ex <- case splitTyConApp_maybe of
        --      Just ex_opt_tc -> 
        --  _ -> fail "wrong options type"
        [ck, c] -> case splitTyConApp_maybe c of
          Just (tc', []) | Just cls <- tyConClass_maybe tc' -> do
            res <- unsafeTcPluginTcM (setCtLocM (ctLoc ct) $ check cls (not get_result))
            ev_term <- if get_result
              then mk_check_result_inst ck tc' res
              else mk_check_inst ck tc'
            return $ Just (ev_term, ct)
              
          _ -> return Nothing
          
          
        _ -> fail "wrong class app type"
  _ -> return Nothing

check :: Class -> Bool -> TcM (Bool, Bool)
check cls fail_on_err = do
  maybe_ex_msg <- check_exhaustiveness cls
  ex_res <- res_or_fail maybe_ex_msg
  inst_envs <- tcGetInstEnvs
  term_msgs <- mapMaybeM check_inst (classInstances inst_envs cls)
  term_res <- res_or_fail (listToMaybe term_msgs)
  return (ex_res, term_res)
  where
    res_or_fail (Just m) = if fail_on_err then failWithTotal m else return False
    res_or_fail Nothing = return True

    check_inst inst = do
      let dfun_type = idType $ is_dfun inst
      let (theta, tau) = splitInstTyForValidity dfun_type
      checkPaterson $ tryTc $ checkInstTermination theta tau

check_exhaustiveness :: Class -> TcM (Maybe TotalClassCheckerMessage)
check_exhaustiveness cls = do
  let name = mkName $ occNameString $ nameOccName $ className cls
  let match_on = mapMaybe match_on_bndr $ tyConBinders (classTyCon cls)
  binds <- checkTcRnResult $ tryTc $ do
    ev_fun_dec <- runQuasi (mkEvidenceFun name match_on)
    ev_fun_binds <- case convertToHsDecls (Generated DoPmc) noSrcSpan ev_fun_dec of
      Left err -> failWithTc $ TcRnTHError (THSpliceFailed (RunSpliceFailure err))
      Right ev_fun_binds -> return ev_fun_binds
    (group, Nothing) <- findSplice ev_fun_binds
    (gbl_rn, rn_group) <- updGblEnv (\env -> env{tcg_binds=emptyBag}) $ rnTopSrcDecls group
    ((gbl_tc, _), _) <- captureTopConstraints $ setGblEnv gbl_rn $ tcTopSrcDecls rn_group
    (_, _, binds, _, _, _) <- setGblEnv gbl_tc $ zonkTopDecls emptyBag (tcg_binds gbl_tc) [] [] [] 
    return binds
  checkDsResult cls $ updTopFlags (flip wopt_set Opt_WarnIncompletePatterns) $ initDsTc $ dsTopLHsBinds binds
  where
    match_on_bndr (Bndr _ (NamedTCB _)) = Nothing
    match_on_bndr (Bndr var AnonTCB) = Just $ isAlgType (tyVarKind var)


mk_check_inst :: Type -> TyCon -> TcPluginM EvTerm
mk_check_inst ck tc = do
  check_class <- getCheckClass
  tot_ev_tc <- getTotalityEvidenceType
  let c_ty = mkTyConTy tc
  let tot_ev_ty = mkTyConApp tot_ev_tc [ck, c_ty]
  let check_dc = tyConSingleDataCon (classTyCon check_class)
  return $ EvExpr $ mkCoreConApps check_dc [Type ck, Type c_ty, mkImpossibleExpr tot_ev_ty "TotalityEvidence"]

mk_check_result_inst :: Type -> TyCon -> (Bool, Bool) -> TcPluginM EvTerm
mk_check_result_inst ck tc (ex_res, term_res) = do
  check_result_class <- getCheckResultClass
  let c_ty = mkTyConTy tc
  let check_result_dc = tyConSingleDataCon (classTyCon check_result_class)
  return $ EvExpr $ mkCoreConApps check_result_dc [Type ck, Type c_ty, boolToCoreExpr ex_res, boolToCoreExpr term_res]

boolToCoreExpr :: Bool -> CoreExpr
boolToCoreExpr False = mkConApp falseDataCon []
boolToCoreExpr True = mkConApp trueDataCon []

splitInstTyForValidity :: Type -> (ThetaType, Type)
splitInstTyForValidity = split_context [] . drop_foralls
  where
    -- This is like 'dropForAlls', except that it does not look through type
    -- synonyms.
    drop_foralls :: Type -> Type
    drop_foralls (ForAllTy (Bndr _tv argf) ty)
      | isInvisibleForAllTyFlag argf = drop_foralls ty
    drop_foralls ty = ty

    -- This is like 'tcSplitPhiTy', except that it does not look through type
    -- synonyms.
    split_context :: ThetaType -> Type -> (ThetaType, Type)
    split_context preds (FunTy { ft_af = af, ft_arg = pred', ft_res = tau })
      | isInvisibleFunArg af = split_context (pred':preds) tau
    split_context preds ty = (reverse preds, ty)

checkInstTermination :: ThetaType -> TcPredType -> TcM ()
-- See Note [Paterson conditions]
checkInstTermination theta head_pred
  = check_preds emptyVarSet theta
  where
   head_size = pSizeType head_pred
   -- This is inconsistent and probably wrong.  pSizeType does not filter out
   -- invisible type args (making the instance head look big), whereas the use of
   -- pSizeClassPredX below /does/ filter them out (making the tested constraints
   -- look smaller). I'm sure there is non termination lurking here, but see #15177
   -- for why I didn't change it. See Note [Invisible arguments and termination]
   -- in GHC.Tc.Utils.TcType

   check_preds :: VarSet -> [PredType] -> TcM ()
   check_preds foralld_tvs preds = mapM_ (check' foralld_tvs) preds

   check' :: VarSet -> PredType -> TcM ()
   check' foralld_tvs pred'
     = case classifyPredType pred' of
         EqPred {}      -> return ()  -- See #4200.
         IrredPred {}   -> check2 (pSizeTypeX foralld_tvs pred')

         ClassPred cls tys
           | isCTupleClass cls  -- See Note [Tuples in checkInstTermination]
           -> check_preds foralld_tvs tys

           | otherwise          -- Other ClassPreds
           -> check2 (pSizeClassPredX foralld_tvs cls tys)

         ForAllPred tvs _ head_pred'
           -> check' (foralld_tvs `extendVarSetList` tvs) head_pred'
              -- Termination of the quantified predicate itself is checked
              -- when the predicates are individually checked for validity

      where
        check2 pred_size
          = case pred_size `ltPatersonSize` head_size of
              Just pc_failure -> failWithTc $ TcRnPatersonCondFailure pc_failure InInstanceDecl pred' head_pred
              Nothing         -> return ()
