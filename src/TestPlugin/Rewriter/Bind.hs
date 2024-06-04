{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter.Bind (rewriteBinds) where

import Data.Foldable (forM_, Foldable (toList))

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (EvBind, eb_lhs, eb_rhs), TcEvBinds (TcEvBinds, EvBinds), isIdHsWrapper)
import GHC (GhcTc, HsBindLR (..), AbsBinds (..), ABExport (abe_mono, abe_poly, ABE, abe_wrap), TyThing (AnId), MatchGroupTc (MatchGroupTc), MatchGroup (mg_ext, MG))
import Data.Generics (everywhereM, mkM, mkT, everywhere)
import Control.Monad.State (modify, State, runState, MonadState (put, get))
import GHC.Data.Bag (filterBagM)
import TestPlugin.Placeholder (isPlaceholder)
import GHC.Tc.Utils.TcType (mkPhiTy, mkTyCoVarTy, mkTyCoVarTys, substTy)
import Data.Maybe (mapMaybe, fromMaybe, fromJust, isJust)
import GHC.Tc.Utils.Monad (newTcRef, setGblEnv, getGblEnv, readTcRef, updTcRef, writeTcRef)
import GHC.Tc.Utils.Env (tcExtendGlobalEnvImplicit)
import GHC.Types.Unique.DFM (plusUDFM)
import GHC.Core.TyCo.Rep (Type (..))

import TestPlugin.Rewriter.Env
import TestPlugin.Rewriter.Utils
import GHC.Tc.Utils.Unify (unifyType)
import GHC.Core.Unify (tcUnifyTy, alwaysBindFun, tcUnifyTys, matchBindFun)
import GHC.Hs.Syn.Type (hsWrapperType)
import Control.Monad (unless)

rewriteBinds :: TcGblEnv -> (UpdateEnv -> TcGblEnv -> TcM TcGblEnv) -> TcM TcGblEnv
rewriteBinds gbl cont = do
  printLnTcM "rewriteBinds {"
  let binds = tcg_binds gbl
  updateEnv <- newTcRef emptyDNameEnv
  binds' <- everywhereM (mkM (rewriteXHsBindsLR updateEnv)) binds
  --printLnTcM "Starting second pass"
  --binds'' <- everywhereM (mkM (rewriteFunBind updateEnv)) binds'
  printLnTcM "Finished rewriteBinds pass, checking for remaining placeholders"
  binds'' <- everywhereM (mkM assertNoPlaceholders) binds'
  updates <- readTcRef updateEnv
  setGblEnv gbl{tcg_binds = binds''} $ tcExtendGlobalEnvImplicit ((\UInfo{new_id=id'} -> AnId id') <$> toList updates) $ do
    gbl' <- getGblEnv
    printLnTcM "}"
    cont updates gbl'

rewriteXHsBindsLR :: TcRef UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteXHsBindsLR updateEnv (XHsBindsLR ab@(AbsBinds {abs_exports=exports, abs_binds=inner_binds})) = do
  --printLnTcM "rewriteXHsBindsLR {"
  newUpdateEnv <- newTcRef emptyDNameEnv
  inner_binds' <- mapM (traverse $ rewriteFunBind newUpdateEnv) inner_binds
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
        else fail "Rewrite inside AbsBinds with non-identity abe_wrap"

rewriteFunBind :: TcRef UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteFunBind updateEnv b@(FunBind {fun_id=(L loc fid), fun_ext=(wrapper, ctick), fun_matches=MG{mg_ext=(MatchGroupTc args res _)} }) = do
  outputTcM "rewriteFunBind " fid
  printWrapper 1 wrapper
  let old_ty = varType fid
  let wrapped = hsWrapperType wrapper $ mkScaledFunTys args res
  let old_vars = mapMaybe namedBinderVar $ fst $ splitInvisPiTys old_ty
  let w_vars = mapMaybe namedBinderVar $ fst $ splitInvisPiTys wrapped
  let maybe_subst = tcUnifyTys (matchBindFun (mkVarSet w_vars)) (mkTyCoVarTys w_vars) (mkTyCoVarTys old_vars)
  newArgsRef <- newTcRef []
  wrapper' <- everywhereM (mkM (rewriteWpLet newArgsRef)) wrapper
  ev_vars <- readTcRef newArgsRef
  case (ev_vars, maybe_subst) of
    ([], _) -> return b
    (_, Nothing) -> fail "Failed to unify function type"
    (ev_vars', Just subst) -> do
      dFlags <- getDynFlags
      printLnTcM $ "rewriteFunBind " ++ (showSDoc dFlags $ ppr fid) ++ " {"
      (wrapper'', last_tv) <- insertWpEvLams ev_vars' wrapper'
      outputTcM "new wrapper: " ()
      printWrapper 1 wrapper''
      let theta' = substTheta subst (map varType ev_vars')
      last_tv' <- case substTyVar subst last_tv of
        TyVarTy tv -> return tv
        _ -> fail "substitution assigned last tv to something other than a tv"
      let rewrapped = substTy subst $ hsWrapperType wrapper'' $ mkScaledFunTys args res
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
      return b {fun_id=L loc fid', fun_ext=(wrapper'', ctick)}
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
      unless (length old_flags == length new_flags) $ fail "number of foralls changed, bug"
      let (result, remaining_flags) = everywhereM (mkM set_flag) tgt `runState` reverse old_flags
      unless (null remaining_flags) $ error "impossible"
      let set_flags = get_flags result
      outputTcM "set flags" set_flags
      unless (old_flags == set_flags) $ fail "flag setting failed"
      return result
rewriteFunBind _ b = return b

namedBinderVar :: PiTyBinder -> Maybe TyCoVar
namedBinderVar (Named (Bndr var _)) = Just var
namedBinderVar _ = Nothing

rewriteWpLet :: TcRef [EvVar] -> HsWrapper -> TcM HsWrapper
rewriteWpLet _ (WpLet (TcEvBinds _)) = fail "Encountered unzonked TcEvBinds, this should not happen"
rewriteWpLet newArgsRef (WpLet (EvBinds binds)) = do
  --printLnTcM "rewriteWpLet {"
  let (binds', evVars) = runState (filterBagM isNotPlaceholder binds) []
  updTcRef newArgsRef (++ evVars)
  --printLnTcM "}"
  return $ WpLet (EvBinds binds')
rewriteWpLet _ w = return w

isNotPlaceholder :: EvBind -> State [EvVar] Bool
isNotPlaceholder (EvBind {eb_lhs=evVar, eb_rhs=evTerm})
  | isPlaceholder evTerm = do
    modify (evVar :)
    return False
  | otherwise = return True

-- insert an EvLam for each var next to the rightmost TyLam
insertWpEvLams :: [EvVar] -> HsWrapper -> TcM (HsWrapper, TyVar)
insertWpEvLams ev_vars wrap = do 
  tv_ref <- newTcRef Nothing
  w' <- go1 tv_ref wrap
  tv <- readTcRef tv_ref
  case tv of
    Nothing -> fail "Failed to insert WpEvLams"
    Just tv' -> return (w', tv')
  where
    go1 tv_ref w = do
      tv <- readTcRef tv_ref
      if isJust tv then return w else go2 tv_ref w

    go2 tv_ref (WpCompose w1 w2) = do
      w2' <- go1 tv_ref w2
      w1' <- go1 tv_ref w1
      return $ WpCompose w1' w2'
    go2 _ w@(WpFun _ _ _) = do
      outputTcM "Found WpFun" w
      fail "WpFun not supported"
    go2 tv_ref w@(WpTyLam tv) = do
      writeTcRef tv_ref (Just tv)
      let w' = foldr ((<.>) . WpEvLam) WpHole ev_vars
      return $ w <.> w'
    go2 _ w = return w

      
  

assertNoPlaceholders :: HsWrapper -> TcM HsWrapper
assertNoPlaceholders w@(WpLet (EvBinds binds))
  | any (isPlaceholder . eb_rhs) binds = do 
    outputTcM "Placeholders remaining in wrapper: " ()
    printWrapper 1 w
    fail "Found placeholder after rewrites"
  | otherwise = return w
assertNoPlaceholders w = return w
