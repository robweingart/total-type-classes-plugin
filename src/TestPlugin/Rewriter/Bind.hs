{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter.Bind (rewriteBinds) where

import Data.Foldable (forM_, Foldable (toList))

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef, TcLclEnv)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (EvBind, eb_lhs, eb_rhs), TcEvBinds (TcEvBinds, EvBinds), isIdHsWrapper)
import GHC (GhcTc, HsBindLR (..), AbsBinds (..), ABExport (abe_mono, abe_poly, ABE, abe_wrap), TyThing (AnId), MatchGroupTc (MatchGroupTc), MatchGroup (mg_ext, MG), LHsBind, HsBind, LHsBinds)
import Data.Generics (everywhereM, mkM)
import Control.Monad.State (modify, State, runState, MonadState (put, get))
import GHC.Data.Bag (filterBagM)
import TestPlugin.Placeholder (isPlaceholder)
import GHC.Tc.Utils.TcType (mkTyCoVarTys, substTy)
import Data.Maybe (mapMaybe)
import GHC.Tc.Utils.Monad (newTcRef, readTcRef, updTcRef, wrapLocMA, updGblEnv)
import GHC.Tc.Utils.Env (tcExtendGlobalEnvImplicit)
import GHC.Types.Unique.DFM (plusUDFM)
import GHC.Core.TyCo.Rep (Type (..))

import TestPlugin.Rewriter.Env
import TestPlugin.Rewriter.Utils
import GHC.Core.Unify (matchBindFun, tcUnifyTys)
import GHC.Hs.Syn.Type (hsWrapperType)
import Control.Monad (unless)

rewriteBinds :: LHsBinds GhcTc -> (UpdateEnv -> LHsBinds GhcTc -> TcM (TcGblEnv, TcLclEnv)) -> TcM (TcGblEnv, TcLclEnv)
rewriteBinds binds cont = do
  outputFullTcM "Full before rewriteBinds: " binds
  printLnTcM "rewriteBinds {"
  updateEnv <- newTcRef emptyDNameEnv
  binds' <- everywhereM (mkM (rewriteLHsBind updateEnv)) binds
  --printLnTcM "Starting second pass"
  --binds'' <- everywhereM (mkM (rewriteFunBind updateEnv)) binds'
  printLnTcM "Finished rewriteBinds pass, checking for remaining placeholders"
  binds'' <- everywhereM (mkM checkDoneLHsBind) binds'
  updates <- readTcRef updateEnv
  updGblEnv (\gbl -> gbl{tcg_binds=binds''}) $ tcExtendGlobalEnvImplicit (map (AnId . new_id) $ toList updates) $ do
    printLnTcM "}"
    cont updates binds''

rewriteLHsBind :: TcRef UpdateEnv -> LHsBind GhcTc -> TcM (LHsBind GhcTc)
rewriteLHsBind ref = wrapLocMA (rewriteXHsBindsLR ref)

rewriteXHsBindsLR :: TcRef UpdateEnv -> HsBind GhcTc -> TcM (HsBind GhcTc)
rewriteXHsBindsLR updateEnv (XHsBindsLR ab@(AbsBinds {abs_exports=exports, abs_binds=inner_binds})) = do --printLnTcM "rewriteXHsBindsLR {"
  newUpdateEnv <- newTcRef emptyDNameEnv
  inner_binds' <- mapM (wrapLocMA (rewriteFunBind newUpdateEnv)) inner_binds
  exports' <- mapM (rewriteABExport newUpdateEnv) exports
  newUpdates <- readTcRef newUpdateEnv
  updTcRef updateEnv (plusUDFM newUpdates)
  --printLnTcM "}"
  return $ XHsBindsLR ab{abs_binds=inner_binds',abs_exports=exports'}
rewriteXHsBindsLR _ b = return b

rewriteABExport :: TcRef UpdateEnv -> ABExport -> TcM ABExport
rewriteABExport updateEnv e@ABE{abe_mono=mono, abe_poly=poly, abe_wrap=wrap} = do
  --printLnTcM "rewriteABExport {"
  updates <- readTcRef updateEnv
  if isEmptyDNameEnv updates then return e else do
    case lookupDNameEnv updates (varName mono) of
      Nothing -> return e
      Just u -> do
        --printLnTcM "rewriteABExport {"
        if isIdHsWrapper wrap then do
          let newMono = new_id u
          let newPoly = setVarType poly (varType newMono)
          updTcRef updateEnv (\env -> delFromDNameEnv env (varName mono))
          updTcRef updateEnv (\env -> extendDNameEnv env (varName poly) u{new_id=newPoly})
          --printLnTcM "}"
          return e{abe_mono=newMono,abe_poly=newPoly}
        else failTcM $ text "Rewrite inside AbsBinds with non-identity abe_wrap"

rewriteFunBind :: TcRef UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteFunBind updateEnv b@(FunBind {fun_id=(L loc fid), fun_ext=(wrapper, ctick), fun_matches=MG{mg_ext=(MatchGroupTc args res _)} }) = do
  let old_ty = varType fid
  let wrapped = hsWrapperType wrapper $ mkScaledFunTys args res
  let old_vars = mapMaybe namedBinderVar $ fst $ splitInvisPiTys old_ty
  let w_vars = mapMaybe namedBinderVar $ fst $ splitInvisPiTys wrapped
  let maybe_subst = tcUnifyTys (matchBindFun (mkVarSet w_vars)) (mkTyCoVarTys w_vars) (mkTyCoVarTys old_vars)
  wrapper_res <- rewriteHsWrapper wrapper
  case (wrapper_res, maybe_subst) of
    (Nothing, _) -> return b
    (_, Nothing) -> failTcM $ text "Failed to unify fun type"
    (Just (wrapper', theta, last_tv), Just subst) -> do
      dFlags <- getDynFlags
      printLnTcM $ "rewriteFunBind " ++ (showSDoc dFlags $ ppr fid) ++ " {"
      printLnTcM "old wrapper: "
      printWrapper 1 wrapper
      printLnTcM "new wrapper: "
      printWrapper 1 wrapper'
      let theta' = substTheta subst theta
      last_tv' <- case substTyVar subst last_tv of
        TyVarTy tv -> return tv
        _ -> failTcM $ text "substitution assigned last tv to something other than a tv"
      let rewrapped = substTy subst $ hsWrapperType wrapper' $ mkScaledFunTys args res
      new_ty <- copy_flags old_ty rewrapped
      let fid' = setVarType fid new_ty
      let uinfo = UInfo{new_id=fid',old_type=old_ty,new_theta=theta',last_ty_var=last_tv'}
      --outputTcM "Modified id: " fid'
      --outputTcM "Old type: " oldTy
      --printBndrTys oldTy
      outputTcM "New type: " $ varType fid'
      printBndrTys $ varType fid'
      outputTcM "New theta: " theta'
      forM_ theta' $ \case
        TyConApp _ [TyVarTy var] -> outputTcM "  type var in theta: " $ varUnique var
        _ -> return ()
      updTcRef updateEnv (\env -> extendDNameEnv env (varName fid') uinfo)
      printLnTcM "}"
      return b {fun_id=L loc fid', fun_ext=(wrapper', ctick)}
  where
    add_flag :: ForAllTyFlag -> State [ForAllTyFlag] ForAllTyFlag
    add_flag flag = modify (flag :) >> return flag

    get_flags :: Type -> [ForAllTyFlag]
    get_flags ty = snd $ everywhereM (mkM add_flag) ty `runState` []

    set_flag :: ForAllTyFlag -> State [ForAllTyFlag] ForAllTyFlag
    set_flag _ = do
      fs <- get
      case fs of
        [] -> error "impossible"
        (f : fs') -> do
          put fs'
          return f

    copy_flags :: Type -> Type -> TcM Type
    copy_flags src tgt = do
      let old_flags = get_flags src
      outputTcM "old flags" old_flags
      let new_flags = get_flags tgt
      outputTcM "new flags" new_flags
      unless (length old_flags == length new_flags) $ failTcM $ text "number of foralls changed, bug"
      let (result, remaining_flags) = everywhereM (mkM set_flag) tgt `runState` reverse old_flags
      unless (null remaining_flags) $ error "impossible"
      let set_flags = get_flags result
      outputTcM "set flags" set_flags
      unless (old_flags == set_flags) $ failTcM $ text "flag setting failed"
      return result
rewriteFunBind _ b = return b

namedBinderVar :: PiTyBinder -> Maybe TyCoVar
namedBinderVar (Named (Bndr var _)) = Just var
namedBinderVar _ = Nothing

rewriteHsWrapper :: HsWrapper -> TcM (Maybe (HsWrapper, [PredType], TyVar))
rewriteHsWrapper wrapper = do
  --printLnTcM "rewriteHsWrapper {"
  newArgsRef <- newTcRef []
  wrapper' <- everywhereM (mkM (rewriteWpLet newArgsRef)) wrapper
  tys <- readTcRef newArgsRef
  res <- case tys of
    [] -> return Nothing
    [[]] -> return Nothing
    [newArgTys] -> do
      tv <- lastTyVar wrapper
      return $ Just (wrapper', newArgTys, tv) 
    _ -> failTcM $ text "encountered multiple zonked WpLet, this should not happen"
  --printLnTcM "}"
  return res

rewriteWpLet :: TcRef [[PredType]] -> HsWrapper -> TcM HsWrapper
rewriteWpLet _ (WpLet (TcEvBinds _)) = failTcM $ text "Encountered unzonked TcEvBinds, this should not happen"
rewriteWpLet newArgsRef (WpLet (EvBinds binds)) = do
  --printLnTcM "rewriteWpLet {"
  let (binds', evVars) = runState (filterBagM isNotPlaceholder binds) []
  updTcRef newArgsRef ((varType <$> evVars) :)
  --printLnTcM "}"
  return $ foldr ((<.>) . WpEvLam) (WpLet (EvBinds binds')) evVars
rewriteWpLet _ w = return w

isNotPlaceholder :: EvBind -> State [EvVar] Bool
isNotPlaceholder (EvBind {eb_lhs=evVar, eb_rhs=evTerm})
  | isPlaceholder evTerm = do
    modify (evVar :)
    return False
  | otherwise = return True

lastTyVar :: HsWrapper -> TcM TyVar
lastTyVar w = go w >>= \case
  Nothing -> failTcM (text "Wrapper has no WpTyLam" <+> ppr w)
  Just tv -> return tv
  where
    go WpHole = return Nothing
    go (WpCompose w1 w2) = go w2 >>= \case
      Nothing -> go w1
      Just tv -> return $ Just tv
    go (WpTyLam tv) = return $ Just tv
    go (WpFun _ _ _) = failTcM (text "unexpected WpFun inside " <+> ppr w)
    go _ = return Nothing

checkDoneLHsBind :: LHsBind GhcTc -> TcM (LHsBind GhcTc)
checkDoneLHsBind = wrapLocMA checkDoneFunBind

checkDoneFunBind :: HsBind GhcTc -> TcM (HsBind GhcTc)
checkDoneFunBind fb@(FunBind {fun_ext=(wrap, _)}) = checkDoneHsWrapper wrap >> return fb
checkDoneFunBind b = return b

checkDoneHsWrapper :: HsWrapper -> TcM HsWrapper
checkDoneHsWrapper w@(WpLet (EvBinds binds))
  | any (isPlaceholder . eb_rhs) binds = do 
    outputTcM "Placeholders remaining in wrapper: " ()
    printWrapper 1 w
    failTcM $ text "Found placeholder after rewrites"
  | otherwise = return w
checkDoneHsWrapper w = return w
