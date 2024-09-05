{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}

module TotalClassPlugin.Checker.Solve ( solveCheck ) where

import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types.Evidence (EvTerm (EvExpr))
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc)
import GHC.Tc.Types (TcM, TcGblEnv (tcg_binds))
import GHC (Class, instanceDFunId)
import Data.Maybe (mapMaybe, maybeToList)
import GHC.Core.Class (Class(classTyCon, className))
import GHC.ThToHs (convertToHsDecls, convertToHsType, thRdrNameGuesses)
import GHC.Rename.Module (findSplice)
import GHC.Tc.Module (rnTopSrcDecls, tcTopSrcDecls)
import GHC.Tc.Solver (captureTopConstraints)
import GHC.Tc.Utils.Monad (setGblEnv, updTopFlags, updGblEnv, failWithTc, setCtLocM, tryTc, mapAndUnzipM, newSysName, newSysLocalId, mapAndUnzip3M)
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
import TotalClassPlugin.Checker.Errors (checkDsResult, TotalClassCheckerMessage (..), checkTcRnResult, failWithTotal, checkPaterson, checkQuasiError)
import GHC.Data.Maybe (listToMaybe)
import TotalClassPlugin.GHCUtils (checkInstTermination, splitInstTyForValidity)
import TotalClassPlugin.Rewriter.Utils (outputTcM, failTcM)
import GHC.Tc.Utils.TcType (tyCoVarsOfTypesList)
import GHC.Tc.Utils.Instantiate (tcInstSkolTyVars, instDFunType)
import GHC.Tc.Types.Origin (unkSkol)
import GHC.Core.Unify (tcUnifyTysFG, UnifyResultM (..))
import GHC.Core.TyCo.Rep (Type(..))
import Data.Foldable (Foldable(toList), forM_)
import Language.Haskell.TH.Syntax (mkNameU)
import GHC.Types.Unique (getKey)
import Data.Functor.Compose (Compose(Compose, getCompose))
import Control.Monad.State (StateT (..), get, MonadState (..), lift)

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
    checkClass <- getCheckClass
    checkResultClass <- getCheckResultClass
    let maybe_fail_on_err = if | targetClass == checkClass -> Just True
                               | targetClass == checkResultClass -> Just False
                               | otherwise -> Nothing
    case maybe_fail_on_err of
      Nothing -> do 
        return Nothing
      Just fail_on_err -> case tys of
        [ck, c] -> check_inner ct ck c fail_on_err
        _ -> return Nothing
  _ -> do
    tcPluginIO $ putStrLn "not a class predicate"
    return Nothing

check_inner :: Ct -> Type -> PredType -> Bool -> TcPluginM (Maybe (EvTerm, Ct))
check_inner ct ck c fail_on_err = case classifyPredType c of
  ForAllPred _ _ inner -> check_inner ct ck inner fail_on_err
  ClassPred cls args -> do
    let do_check = case args of { [] -> check cls fail_on_err; _ -> checkConstraint cls args fail_on_err }
    res <- unsafeTcPluginTcM (setCtLocM (ctLoc ct) do_check)
    ev_term <- if fail_on_err
      then mk_check_inst ck cls
      else mk_check_result_inst ck cls res
    return $ Just (ev_term, ct)
  _ -> return Nothing

data CheckState = FailOnError | CollectErrors Bool Bool Bool
type CM a = StateT CheckState TcM a
data CheckName = Exhaustiveness | Termination | Context

failCM :: CheckName -> TotalClassCheckerMessage -> CM ()
failCM which message = get >>= \case
  FailOnError -> lift $ failWithTotal message
  CollectErrors ex term cxt -> put $ case which of
    Exhaustiveness -> CollectErrors False term cxt
    Termination -> CollectErrors ex False cxt
    Context -> CollectErrors ex term False

maybeFailCM :: CheckName -> Maybe TotalClassCheckerMessage -> CM ()
maybeFailCM _ Nothing = return ()
maybeFailCM which (Just message) = failCM which message

checkConstraint :: Class -> [Type] -> Bool -> TcM (Bool, Bool, Bool)
checkConstraint cls args fail_on_err = runStateT (checkConstraint' cls args) initial >>= \case
  ((), FailOnError) -> return (True, True, True)
  ((), CollectErrors ex term cxt) -> return (ex, term, cxt)
  where
    initial = if fail_on_err then FailOnError else CollectErrors True True True

checkConstraint' :: Class -> [Type] -> CM ()
checkConstraint' cls args = do
  (vars, tys) <- lift $ inst_vars args
  results <- lift $ get_all_unifiers cls tys
  let initial_ids = mkUniqSet $ map instanceDFunId results
  types <- mapM (check_instance cls tys vars initial_ids) results
  ev_fun <- lift $ withThTypes (Compose types) (mkEvidenceFun2 . getCompose)
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

check_instance :: Class -> [Type] -> [TyVar] -> UniqSet Id -> ClsInst -> CM [Type]
check_instance cls tys vars initial_ids inst = do
  lift (check_termination inst) >>= maybeFailCM Termination
  let res = tcUnifyTysFG instanceBindFun (is_tys inst) tys
  case res of 
    Unifiable subst_inst -> do
      let mb = map (lookupTyVar subst_inst) (is_tvs inst)   
      (_, cxt) <- lift $ instDFunType (is_dfun inst) mb
      let cxt' = substTheta subst_inst cxt
      forM_ cxt' (check_cxt_constraint cls inst initial_ids) 
      let patterns = substTys subst_inst (TyVarTy <$> vars)
      return patterns
    MaybeApart _ _ -> lift $ failTcM $ text "bug! instance returned from lookup is MaybeApart"
    SurelyApart -> lift $ failTcM $ text "bug! instance returned from lookup is SurelyApart"

check_cxt_constraint :: Class -> ClsInst -> UniqSet Id -> PredType -> CM ()
check_cxt_constraint cls inst initial_ids pred_ty 
  | ClassPred cls' tys <- classifyPredType pred_ty = if
    | cls' == cls -> do
      (_, tys') <- lift $ inst_vars tys
      inst_ids <- (mkUniqSet . map instanceDFunId) <$> (lift $ get_all_unifiers cls tys')
      let escaping_ids = minusUniqSet inst_ids (initial_ids)
      if isEmptyUniqSet escaping_ids then return () else failCM Context TotalError
    | otherwise ->  failCM Context (TotalCheckerInvalidContext pred_ty (idType (instanceDFunId inst)))
  | otherwise = failCM Context TotalError

check_termination :: ClsInst -> TcM (Maybe TotalClassCheckerMessage)
check_termination = checkPaterson . tryTc . uncurry checkInstTermination . splitInstTyForValidity . idType . is_dfun

withThTypes :: Traversable t => t Type -> (t TH.Type -> TH.Q a) -> TcM (Either TotalClassCheckerMessage a)
withThTypes types thing_inside = do
  ty_ids <- mapM (newSysLocalId (fsLit "temp") OneTy) types
  tcExtendIdEnv (toList ty_ids) $ checkQuasiError $ do
    th_types <- mapM (reifyType . mkNameU "temp" . toInteger . getKey . idUnique) ty_ids
    thing_inside th_types

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

