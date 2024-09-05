{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}

module TotalClassPlugin.Checker.Solve ( solveCheck ) where

import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types.Evidence (EvTerm (EvExpr))
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc)
import GHC.Tc.Types (TcM, TcGblEnv (tcg_binds))
import GHC (Class)
import Data.Maybe (mapMaybe, maybeToList)
import GHC.Core.Class (Class(classTyCon, className))
import GHC.ThToHs (convertToHsDecls, convertToHsType, thRdrNameGuesses)
import GHC.Rename.Module (findSplice)
import GHC.Tc.Module (rnTopSrcDecls, tcTopSrcDecls)
import GHC.Tc.Solver (captureTopConstraints)
import GHC.Tc.Utils.Monad (setGblEnv, updTopFlags, updGblEnv, failWithTc, setCtLocM, tryTc, mapAndUnzipM, newSysName, newSysLocalId)
import GHC.HsToCore.Monad (initDsTc)
import GHC.HsToCore.Binds (dsTopLHsBinds)
import GHC.Tc.Zonk.Type (zonkTopDecls)
import GHC.Data.Bag (emptyBag)
import GHC.Tc.Errors.Types (TcRnMessage (TcRnTHError), THError (THSpliceFailed), SpliceFailReason (..))
import TotalClassPlugin.Checker.TH (mkEvidenceFun, mkEvidenceFun2)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH (mkName, reifyType)
import GHC.Core.Predicate (Pred(..), classifyPredType)
import GHC.Core.InstEnv (classInstances, ClsInst (..), lookupInstEnv, getPotentialUnifiers, instanceBindFun)
import GHC.Tc.Utils.Env (tcGetInstEnvs, tcExtendIdEnv)
import TotalClassPlugin.Checker.Errors (checkDsResult, TotalClassCheckerMessage (TotalCheckerInvalidContext), checkTcRnResult, failWithTotal, checkPaterson, checkQuasiError)
import GHC.Data.Maybe (listToMaybe)
import TotalClassPlugin.GHCUtils (checkInstTermination, splitInstTyForValidity)
import TotalClassPlugin.Rewriter.Utils (outputTcM, outputFullTcM, failTcM)
import GHC.Tc.Utils.TcType (tyCoVarsOfTypesList)
import GHC.Tc.Utils.Instantiate (tcInstSkolTyVars, instDFunType)
import GHC.Tc.Types.Origin (unkSkol)
import GHC.Core.Unify (tcUnifyTysFG, UnifyResultM (..))
import GHC.Core.TyCo.Rep (Type(..))
import Data.Foldable (Foldable(toList))
import Language.Haskell.TH.Syntax (mkNameU)
import GHC.Types.Unique (getKey)
import Data.Functor.Compose (Compose(Compose, getCompose))

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
solveCheck ct = do
  --tcPluginIO $ putStrLn ("solveCheck " ++ showPprUnsafe ct)
  solveCheck' ct

solveCheck' :: Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveCheck' ct = case classifyPredType (ctPred ct) of
  ClassPred targetClass tys -> do
    --tcPluginIO $ putStrLn ("target class is " ++ showPprUnsafe targetClass ++ " applied to " ++ showPprUnsafe tys)
    checkClass <- getCheckClass
    checkResultClass <- getCheckResultClass
    let maybe_get_result = if | targetClass == checkClass -> Just False
                              | targetClass == checkResultClass -> Just True
                              | otherwise -> Nothing
    case maybe_get_result of
      Nothing -> do 
        --tcPluginIO $ putStrLn "not CheckTotality(Result)"
        return Nothing
      Just get_result -> case tys of
        [ck, c] | ClassPred cls args <- classifyPredType c -> do
          let do_check = case args of { [] -> check cls (not get_result); _ -> checkConstraint cls args (not get_result) }
          --tcPluginIO $ putStrLn ("starting check: " ++ showPprUnsafe cls)
          res <- unsafeTcPluginTcM (setCtLocM (ctLoc ct) do_check)
          ev_term <- if get_result
            then mk_check_result_inst ck cls res
            else mk_check_inst ck cls
          return $ Just (ev_term, ct)
        --[ck, c] -> do
        --  envs <- getInstEnvs
        --  --tcPluginIO $ putStrLn ("global: " ++ showPprUnsafe (ie_global envs) ++ "local: " ++ showPprUnsafe (ie_local envs))
        --  case classifyPredType c of
        --    ClassPred cls _ -> do 
        --      tcPluginIO $ putStrLn ("wrong app type: " ++ showSDocUnsafe (showAstDataFull c))
        --      --let insts = classInstances envs cls
        --      --tcPluginIO $ putStrLn $ showPprUnsafe insts
        --      --tcPluginIO $ putStrLn $ showPprUnsafe $ map is_dfun_name insts
        --      --tcPluginIO $ putStrLn $ showPprUnsafe $ filter (not . memberInstEnv (ie_local envs)) insts
        --    _ -> return ()
        --  return Nothing
        _ -> return Nothing
  _ -> do
    tcPluginIO $ putStrLn "not a class predicate"
    return Nothing

checkConstraint :: Class -> [Type] -> Bool -> TcM (Bool, Bool, Bool)
checkConstraint cls args fail_on_err = do
  outputTcM "Class: " cls
  outputFullTcM "args: " args
  --forM_ args $ \case
  --  TyVarTy v -> do
  --    outputTcM "overlappable? " $ isOverlappableTyVar v
  --    outputTcM "details: " $ tcTyVarDetails v
  --  _ -> return ()
  inst_envs <- tcGetInstEnvs
  --outputTcM "Insts: " $ classInstances inst_envs cls
  --(subst, new_args) <- unsuper (tyCoVarsOfTypesList args)
  let vars = tyCoVarsOfTypesList args
  (subst, vars') <- tcInstSkolTyVars unkSkol vars
  --let new_args = unsuperVar <$> args
  let tys = substTys subst args
  let (successful, potential, _) = lookupInstEnv False inst_envs cls tys
  let results = (fst <$> successful) ++ getPotentialUnifiers potential
  outputTcM "results: " results
  --forM_ results (inspectResult (TyVarTy <$> vars'))
  (term_res_list, types) <- unzip <$> mapM (check_instance fail_on_err tys vars') results
  let term_res = all id term_res_list
  ev_fun <- withThTypes (Compose types) (mkEvidenceFun2 . getCompose)
  mb_ex_err <- either (return . Just) (check_evidence_fun cls) ev_fun
  ex_res <- res_or_fail fail_on_err mb_ex_err
  return (ex_res, term_res, False)
  where

check_instance :: Bool -> [Type] -> [TyVar] -> ClsInst -> TcM (Bool, [Type])
check_instance fail_on_err tys vars inst = do
  term_res <- check_termination inst >>= res_or_fail fail_on_err
  let res = tcUnifyTysFG instanceBindFun (is_tys inst) tys
  outputTcM "  Unification result: " res
  case res of 
    Unifiable subst_inst -> do
      let mb = map (lookupTyVar subst_inst) (is_tvs inst)   
      (_, cxt) <- instDFunType (is_dfun inst) mb
      outputTcM "  Context: " cxt
      let patterns = substTys subst_inst (TyVarTy <$> vars)
      outputTcM "  Patterns: " patterns
      return (term_res, patterns)
      --th_res <- withThTypes patterns return
      --case th_res of
      --  Left _ -> failTcM $ text "bug! type conversion failed"
      --  Right th_pats -> do
      --    printLnTcM $ "  TH patterns: " ++ show th_pats
      --    return (term_res, th_pats)
    MaybeApart _ _ -> failTcM $ text "bug! instance returned from lookup is MaybeApart"
    SurelyApart -> failTcM $ text "bug! instance returned from lookup is SurelyApart"

res_or_fail :: Bool -> Maybe TotalClassCheckerMessage -> TcM Bool
res_or_fail True (Just m) = failWithTotal m
res_or_fail False (Just _) = return False
res_or_fail _ Nothing = return True

check_termination :: ClsInst -> TcM (Maybe TotalClassCheckerMessage)
check_termination = checkPaterson . tryTc . uncurry checkInstTermination . splitInstTyForValidity . idType . is_dfun

withThTypes :: Traversable t => t Type -> (t TH.Type -> TH.Q a) -> TcM (Either TotalClassCheckerMessage a)
withThTypes types thing_inside = do
  ty_ids <- mapM (newSysLocalId (fsLit "temp") OneTy) types
  tcExtendIdEnv (toList ty_ids) $ checkQuasiError $ do
    th_types <- mapM (reifyType . mkNameU "temp" . toInteger . getKey . idUnique) ty_ids
    thing_inside th_types

cursedReifyType :: Type -> TcM TH.Type
cursedReifyType ty = do
 name <- newSysName (mkVarOcc "temp")
 let tc_id = mkLocalId name OneTy ty
 tcExtendIdEnv [tc_id] $ do
   let th_name = mkName "temp"
   outputTcM "thRdrNameGuesses: " (thRdrNameGuesses th_name)
   quasi_res <- checkQuasiError $ reifyType th_name
   case quasi_res of
     Left _ -> failTcM $ text "this shouldn't happen"
     Right th_ty -> do
       case convertToHsType (Generated DoPmc) noSrcSpan th_ty of
         Left _ -> failTcM $ text "this shouldn't happen"
         Right ty' -> do
           outputTcM "Round-tripped type: " ty'
           --outputTcM "Equal? " $ eqType ty ty'
           return th_ty

--unsuperVar :: TyCoVar -> TyCoVar
--unsuperVar v
--  | isTcTyVar v, SkolemTv skol_info tc_lcl _ <- tcTyVarDetails v = setTcTyVarDetails v (SkolemTv skol_info tc_lcl False)
--  | otherwise = v
    

--unsuper :: [TyCoVar] -> (Subst, [TyCoVar])
--unsuper vars = let (s, vars') = go vars in (s, get_var <$> substTyCoVars s vars')
--  where
--    get_var (TyVarTy v) = v
--    get_var _ = error "impossible"
--
--    go [] = (emptySubst, [])
--    go (v : vs) | isTcTyVar v, SkolemTv skol_info tc_lcl _ <- tcTyVarDetails v = mkTcTyVar ()
  
  

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
      _ -> Just (TotalCheckerInvalidContext tau pred_ty)

    check_context theta tau = mapMaybe (check_pred_type tau) theta

check_evidence_fun :: Class -> [TH.Dec] -> TcM (Maybe TotalClassCheckerMessage)
check_evidence_fun cls decs = do
  binds <- checkTcRnResult $ tryTc $ do
    ev_fun_binds <- case convertToHsDecls (Generated DoPmc) noSrcSpan decs of
      Left err -> failWithTc $ TcRnTHError (THSpliceFailed (RunSpliceFailure err))
      Right ev_fun_binds -> return ev_fun_binds
    (group, Nothing) <- findSplice ev_fun_binds
    (gbl_rn, rn_group) <- updGblEnv (\env -> env{tcg_binds=emptyBag}) $ rnTopSrcDecls group
    ((gbl_tc, _), _) <- captureTopConstraints $ setGblEnv gbl_rn $ tcTopSrcDecls rn_group
    (_, _, binds, _, _, _) <- setGblEnv gbl_tc $ zonkTopDecls emptyBag (tcg_binds gbl_tc) [] [] [] 
    return binds
  checkDsResult cls $ updTopFlags (flip wopt_set Opt_WarnIncompletePatterns) $ initDsTc $ dsTopLHsBinds binds

check_exhaustiveness :: Class -> TcM (Maybe TotalClassCheckerMessage)
check_exhaustiveness cls = do
  let name = mkName $ occNameString $ nameOccName $ className cls
  let arity = length $ tyConBinders (classTyCon cls)
  checkQuasiError (mkEvidenceFun name arity) >>= \case
    Left err -> return (Just err)
    Right decs -> check_evidence_fun cls decs

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

