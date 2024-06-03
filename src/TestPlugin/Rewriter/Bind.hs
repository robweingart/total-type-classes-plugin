{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter.Bind (rewriteBinds) where

import Data.Foldable (forM_, Foldable (toList))

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (EvBind, eb_lhs, eb_rhs), TcEvBinds (TcEvBinds, EvBinds))
import GHC (GhcTc, HsBindLR (..), AbsBinds (..), ABExport (abe_mono, abe_poly, ABE, abe_wrap), TyThing (AnId))
import Data.Generics (everywhereM, mkM, mkT, everywhere)
import Control.Monad.State (modify, State, runState)
import GHC.Data.Bag (filterBagM)
import TestPlugin.Placeholder (isPlaceholder)
import GHC.Tc.Utils.TcType (mkPhiTy)
import Data.Maybe (mapMaybe, fromMaybe)
import GHC.Tc.Utils.Monad (newTcRef, setGblEnv, getGblEnv, readTcRef, updTcRef)
import GHC.Tc.Utils.Env (tcExtendGlobalEnvImplicit)
import GHC.Types.Unique.DFM (plusUDFM)
import GHC.Core.TyCo.Rep (Scaled (..), Type (..))

import TestPlugin.Rewriter.Env
import TestPlugin.Rewriter.Utils

rewriteBinds :: TcGblEnv -> (UpdateEnv -> TcGblEnv -> TcM TcGblEnv) -> TcM TcGblEnv
rewriteBinds gbl cont = do
  let binds = tcg_binds gbl
  updateEnv <- newTcRef emptyDNameEnv
  binds' <- everywhereM (mkM (rewriteHsBindLR updateEnv)) binds
  updates <- readTcRef updateEnv
  forM_ updates $ \UInfo{new_id=id', old_type=oldTy, new_theta=newTheta} -> do
   outputTcM "Modified id: " id'
   outputTcM "New type: " $ varType id'
   printBndrTys $ varType id'
   outputTcM "Old type: " oldTy
   printBndrTys oldTy
   outputTcM "New theta: " newTheta
   return ()
  setGblEnv gbl{tcg_binds = binds'} $ tcExtendGlobalEnvImplicit ((\UInfo{new_id=id'} -> AnId id') <$> toList updates) $ do
    gbl' <- getGblEnv
    cont updates gbl'

rewriteHsBindLR :: TcRef UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteHsBindLR updateEnv (XHsBindsLR ab@(AbsBinds {abs_exports=exports, abs_binds=inner_binds})) = do
  newUpdateEnv <- newTcRef emptyDNameEnv
  inner_binds' <- everywhereM (mkM (rewriteInnerHsBindLR newUpdateEnv)) inner_binds
  exports' <- mapM (rewriteABExport newUpdateEnv) exports
  newUpdates <- readTcRef newUpdateEnv
  --lift $ outputTcM "newly added: " newIds
  updTcRef updateEnv (plusUDFM newUpdates)
  return $ XHsBindsLR ab{abs_binds=inner_binds',abs_exports=exports'}
rewriteHsBindLR _ b = return b

rewriteABExport :: TcRef UpdateEnv -> ABExport -> TcM ABExport
rewriteABExport updateEnv e@ABE{abe_mono=mono, abe_poly=poly, abe_wrap=wrap} = do
  updates <- readTcRef updateEnv
  if isEmptyDNameEnv updates then return e else do
    case lookupDNameEnv updates (varName mono) of
      Nothing -> return e
      Just u -> do
        let newMono = new_id u
        let newPoly = setVarType poly (varType newMono)
        --lift $ outputTcM "new_mono: " $ varType newMono
        updTcRef updateEnv (\env -> delFromDNameEnv env (varName mono))
        updTcRef updateEnv (\env -> extendDNameEnv env (varName poly) u{new_id=newPoly})
        --lift $ outputTcM "new_poly: " $ varType newPoly
        --lift $ outputTcM "new_poly invispitys: " $ splitInvisPiTys $ varType newPoly
        --modified' <- get
        --lift $ outputTcM "new_poly (actual): " $ fst <$> lookupDNameEnv modified' (varName poly)
        return e{abe_mono=newMono,abe_poly=newPoly}

rewriteInnerHsBindLR :: TcRef UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteInnerHsBindLR updateEnv b@(FunBind {fun_id=(L loc fid), fun_ext=(wrapper, ctick) }) = do
  result <- rewriteHsWrapper wrapper
  case result of
    Nothing -> return b
    Just (wrapper', newArgTys) -> do
      let oldTy = varType fid
      newTy <- updateFunType oldTy (wrapperBinders wrapper) newArgTys
      outputTcM "new ty: " newTy
      case splitInvisPiTys newTy of
        ([Named (Bndr var _), Anon (Scaled _ (TyConApp _ [TyVarTy var'])) _], _) -> do
          outputTcM "var in ty binder: " $ varUnique var
          outputTcM "var in inst binder: " $ varUnique var'
        _ -> return ()
      let fid' = setVarType fid newTy
      updTcRef updateEnv (\env -> extendDNameEnv env (varName fid') UInfo{new_id=fid',old_type=oldTy,new_theta=newArgTys})
      return b {fun_id=L loc fid', fun_ext=(wrapper', ctick)}
rewriteInnerHsBindLR _ b = return b

wrapperBinders :: HsWrapper -> [Var]
wrapperBinders (WpCompose w1 w2) = wrapperBinders w1 ++ wrapperBinders w2
wrapperBinders (WpTyLam var) = [var]
wrapperBinders _ = []

rewriteHsWrapper :: HsWrapper -> TcM (Maybe (HsWrapper, [PredType]))
rewriteHsWrapper wrapper = do
  newArgsRef <- newTcRef []
  wrapper' <- everywhereM (mkM (rewriteWpLet newArgsRef)) wrapper
  tys <- readTcRef newArgsRef
  case tys of
    [] -> return Nothing
    [[]] -> return Nothing
    [newArgTys] -> return $ Just (wrapper', newArgTys) 
    _ -> fail "encountered multiple WpLet, this should not happen"

rewriteWpLet :: TcRef [[PredType]] -> HsWrapper -> TcM HsWrapper
rewriteWpLet _ (WpLet (TcEvBinds _)) = fail "Encountered unzonked TcEvBinds, this should not happen"
rewriteWpLet newArgsRef (WpLet (EvBinds binds)) = do
  let (binds', evVars) = runState (filterBagM isNotPlaceholder binds) []
  updTcRef newArgsRef ((varType <$> evVars) :)
  return $ foldr ((<.>) . WpEvLam) (WpLet (EvBinds binds')) evVars
rewriteWpLet _ w = return w

isNotPlaceholder :: EvBind -> State [EvVar] Bool
isNotPlaceholder (EvBind {eb_lhs=evVar, eb_rhs=evTerm})
  | isPlaceholder evTerm = do
    modify (evVar :)
    return False
  | otherwise = return True

updateFunType :: Type -> [Var] -> [PredType] -> TcM Type
updateFunType ty wrapper_vars predTys = do
  let predTys' = everywhere (mkT tyVarFor) predTys 
  return $ mkPiTys bndrs $ mkPhiTy predTys' ty'
  where
    (bndrs, ty') = splitInvisPiTys ty
    ty_vars = mapMaybe (\case { Named (Bndr var _) -> Just var; _ -> Nothing }) bndrs
    var_pairs = zip wrapper_vars ty_vars
    tyVarFor var = fromMaybe var (lookup var var_pairs)
