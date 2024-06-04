{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter.Bind (rewriteBinds) where

import Data.Foldable (forM_, Foldable (toList))

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (EvBind, eb_lhs, eb_rhs), TcEvBinds (TcEvBinds, EvBinds), isIdHsWrapper)
import GHC (GhcTc, HsBindLR (..), AbsBinds (..), ABExport (abe_mono, abe_poly, ABE, abe_wrap), TyThing (AnId), MatchGroupTc (MatchGroupTc), MatchGroup (mg_ext, MG))
import Data.Generics (everywhereM, mkM, mkT, everywhere)
import Control.Monad.State (modify, State, runState)
import GHC.Data.Bag (filterBagM)
import TestPlugin.Placeholder (isPlaceholder)
import GHC.Tc.Utils.TcType (mkPhiTy, mkTyCoVarTy, mkTyCoVarTys)
import Data.Maybe (mapMaybe, fromMaybe, fromJust)
import GHC.Tc.Utils.Monad (newTcRef, setGblEnv, getGblEnv, readTcRef, updTcRef)
import GHC.Tc.Utils.Env (tcExtendGlobalEnvImplicit)
import GHC.Types.Unique.DFM (plusUDFM)
import GHC.Core.TyCo.Rep (Type (..))

import TestPlugin.Rewriter.Env
import TestPlugin.Rewriter.Utils
import GHC.Tc.Utils.Unify (unifyType)
import GHC.Core.Unify (tcUnifyTy, alwaysBindFun, tcUnifyTys, matchBindFun)
import GHC.Hs.Syn.Type (hsWrapperType)

rewriteBinds :: TcGblEnv -> (UpdateEnv -> TcGblEnv -> TcM TcGblEnv) -> TcM TcGblEnv
rewriteBinds gbl cont = do
  printLnTcM "rewriteBinds {"
  let binds = tcg_binds gbl
  updateEnv <- newTcRef emptyDNameEnv
  binds' <- everywhereM (mkM (rewriteXHsBindsLR updateEnv)) binds
  --printLnTcM "Starting second pass"
  --binds'' <- everywhereM (mkM (rewriteFunBind updateEnv)) binds'
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
  result <- rewriteHsWrapper wrapper
  case result of
    Nothing -> return b
    Just (wrapper', theta) -> do
      dFlags <- getDynFlags
      printLnTcM $ "rewriteFunBind " ++ (showSDoc dFlags $ ppr fid) ++ " {"
      let old_ty = varType fid
      let (old_bndrs, old_inner) = splitInvisPiTys old_ty
      let (w_bndrs, _) = splitInvisPiTys $ hsWrapperType wrapper $ mkScaledFunTys args res
      let old_vars = mapMaybe namedBinderVar old_bndrs
      let w_vars = mapMaybe namedBinderVar w_bndrs
      let maybeSubst = tcUnifyTys (matchBindFun (mkVarSet w_vars)) (mkTyCoVarTys w_vars) (mkTyCoVarTys old_vars)
      case maybeSubst of
        Nothing -> fail "Failed to unify function type"
        Just subst -> do
          let theta' = substTheta subst theta
          let new_ty = mkPiTys old_bndrs $ mkPhiTy theta' old_inner
          let fid' = setVarType fid new_ty
          let uinfo = UInfo{new_id=fid',old_type=old_ty,new_theta=theta'}
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
rewriteFunBind _ b = return b

namedBinderVar :: PiTyBinder -> Maybe TyCoVar
namedBinderVar (Named (Bndr var _)) = Just var
namedBinderVar _ = Nothing

wrapperBinders :: HsWrapper -> [Var]
wrapperBinders (WpCompose w1 w2) = wrapperBinders w1 ++ wrapperBinders w2
wrapperBinders (WpTyLam var) = [var]
wrapperBinders _ = []

rewriteHsWrapper :: HsWrapper -> TcM (Maybe (HsWrapper, [PredType]))
rewriteHsWrapper wrapper = do
  --printLnTcM "rewriteHsWrapper {"
  newArgsRef <- newTcRef []
  wrapper' <- everywhereM (mkM (rewriteWpLet newArgsRef)) wrapper
  tys <- readTcRef newArgsRef
  res <- case tys of
    [] -> return Nothing
    [[]] -> return Nothing
    [newArgTys] -> return $ Just (wrapper', newArgTys) 
    _ -> fail "encountered multiple WpLet, this should not happen"
  --printLnTcM "}"
  return res

rewriteWpLet :: TcRef [[PredType]] -> HsWrapper -> TcM HsWrapper
rewriteWpLet _ (WpLet (TcEvBinds _)) = fail "Encountered unzonked TcEvBinds, this should not happen"
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

updateFunType :: Type -> [Var] -> [PredType] -> TcM (Type, [PredType])
updateFunType ty wrapper_vars predTys = do
  let predTys' = everywhere (mkT tyVarFor) predTys 
  return $ (mkPiTys bndrs $ mkPhiTy predTys' ty', predTys')
  where
    (bndrs, ty') = splitInvisPiTys ty
    ty_vars = mapMaybe (\case { Named (Bndr var _) -> Just var; _ -> Nothing }) bndrs
    var_pairs = zip wrapper_vars ty_vars
    tyVarFor var = fromMaybe var (lookup var var_pairs)

assertNoPlaceholders :: HsWrapper -> TcM HsWrapper
assertNoPlaceholders w@(WpLet (EvBinds binds))
  | any (isPlaceholder . eb_rhs) binds = do 
    outputTcM "Placeholders remaining in wrapper: " ()
    printWrapper 1 w
    fail "Found placeholder after rewrites"
  | otherwise = return w
assertNoPlaceholders w = return w
