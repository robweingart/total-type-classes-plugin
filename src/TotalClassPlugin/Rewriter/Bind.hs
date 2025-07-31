{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module TotalClassPlugin.Rewriter.Bind (rewriteBinds, removePlaceholdersFromWrapper) where

import Control.Monad (forM_, unless, when)
import Control.Monad.State (MonadState (get, put), State, execState, modify, runState)
import Data.Foldable (Foldable (toList))
import Data.Generics (everywhereM, mkM)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Traversable (mapAccumM)
import GHC (ABExport (ABE, abe_mono, abe_poly, abe_wrap), AbsBinds (..), GhcTc, HsBind, HsBindLR (..), LHsBind, LHsBinds, MatchGroup (MG, mg_ext), MatchGroupTc (MatchGroupTc), TyThing (AnId))
import GHC.Core.TyCo.Rep (Type (..))
import GHC.Core.Unify (matchBindFun, tcUnifyTys)
import GHC.Data.Bag (filterBagM)
import GHC.Hs.Syn.Type (hsWrapperType)
import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcGblEnv (..), TcLclEnv, TcM, TcRef)
import GHC.Tc.Types.Evidence (EvBind (EvBind, eb_lhs, eb_rhs), EvBindsVar (CoEvBindsVar, EvBindsVar, ebv_binds), EvTerm (EvExpr), HsWrapper (..), TcEvBinds (EvBinds, TcEvBinds), evBindMapBinds, isIdHsWrapper, (<.>))
import GHC.Tc.Utils.Env (tcExtendGlobalEnvImplicit)
import GHC.Tc.Utils.Monad (getGblEnv, newTcRef, readTcRef, updGblEnv, updTcRef, wrapLocMA)
import GHC.Tc.Utils.TcType (evVarPred, mkPhiTy, mkTyCoVarTys, substTy)
import GHC.Types.Unique.DFM (plusUDFM)
import TotalClassPlugin.Rewriter.Env
import TotalClassPlugin.Rewriter.Placeholder (getPlaceholderPredType, isPlaceholder)
import TotalClassPlugin.Rewriter.Utils

rewriteBinds :: LHsBinds GhcTc -> (UpdateEnv -> LHsBinds GhcTc -> TcM (TcGblEnv, TcLclEnv)) -> TcM (TcGblEnv, TcLclEnv)
rewriteBinds binds cont = do
  updateEnv <- newTcRef emptyDNameEnv
  binds' <- everywhereM (mkM (rewriteLHsBind updateEnv)) binds
  top_ev_binds <- tcg_ev_binds <$> getGblEnv
  forM_ top_ev_binds $ \ev_bind -> do
    let rhs = eb_rhs ev_bind
    case getPlaceholderPredType rhs of
      Nothing -> return ()
      Just predType -> do
        let fvs = tyCoVarsOfType predType
        if isEmptyUniqSet fvs
          then
            failTcM
              ( text "Missing constraint matches total constraint but has no free type variables:"
                  $$ ppr predType
                  $$ text "Either your constraint is not total, or there is an irreducible type family in the constraint"
              )
          else
            failTcM
              ( text "bug? Placeholder has free variables but ended up as top-level binding"
                  $$ ppr predType
              )
  updates <- readTcRef updateEnv
  updGblEnv (\gbl -> gbl {tcg_binds = binds'}) $ tcExtendGlobalEnvImplicit (map (AnId . new_id) $ toList updates) $ do
    cont updates binds'

rewriteLHsBind :: TcRef UpdateEnv -> LHsBind GhcTc -> TcM (LHsBind GhcTc)
rewriteLHsBind ref = wrapLocMA (rewriteXHsBindsLR ref)

rewriteXHsBindsLR :: TcRef UpdateEnv -> HsBind GhcTc -> TcM (HsBind GhcTc)
rewriteXHsBindsLR
  updateEnv
  ( XHsBindsLR
      ( AbsBinds
          { abs_tvs = tvs,
            abs_ev_vars = ev_vars,
            abs_exports = exports,
            abs_ev_binds = ev_binds,
            abs_binds = inner_binds,
            abs_sig = sig
          }
        )
    ) = do
    newUpdateEnv <- newTcRef emptyDNameEnv
    inner_binds' <- mapM (wrapLocMA (rewriteFunBind newUpdateEnv)) inner_binds
    (added_ev_vars, ev_binds') <- mapAccumM rewrite_ev_binds [] ev_binds
    exports' <- mapM (rewriteABExport newUpdateEnv tvs ev_vars added_ev_vars) exports
    let ev_vars' = added_ev_vars ++ ev_vars
    newUpdates <- readTcRef newUpdateEnv
    updTcRef updateEnv (plusUDFM newUpdates)
    return $
      XHsBindsLR
        ( AbsBinds
            { abs_tvs = tvs,
              abs_ev_vars = ev_vars',
              abs_exports = exports',
              abs_ev_binds = ev_binds',
              abs_binds = inner_binds',
              abs_sig = sig
            }
        )
    where
      rewrite_ev_binds vars ebs = do
        (ev_vars', ev_binds') <- rewriteTcEvBinds ebs
        return (vars ++ ev_vars', ev_binds')
rewriteXHsBindsLR _ b = return b

rewriteABExport :: TcRef UpdateEnv -> [TyVar] -> [EvVar] -> [EvVar] -> ABExport -> TcM ABExport
rewriteABExport updateEnv tvs old_ev_vars added_ev_vars e@ABE {abe_mono = mono, abe_poly = poly, abe_wrap = wrap} = do
  (new_mono, update_from_mono) <- do_mono_update
  let binders = mkTyVarBinders InferredSpec tvs
  let theta = map evVarPred (added_ev_vars ++ old_ev_vars)
  let new_poly =
        setVarType poly $
          mkInvisForAllTys binders $
            mkPhiTy theta $
              idType new_mono
  update_from_abs <-
    if
      | null added_ev_vars -> return Nothing
      | Just last_tv <- listToMaybe (reverse tvs) -> return $ Just (map evVarPred added_ev_vars, last_tv)
      | otherwise -> failTcM $ text "Encountered placeholder in abs_ev_binds, but there are no abs_tvs"
  case (update_from_mono, update_from_abs) of
    (Nothing, Nothing) -> return ()
    (Just (theta_for_update, last_tv), Nothing) -> do_poly_update new_poly theta_for_update last_tv
    (Nothing, Just (theta_for_update, last_tv)) -> do_poly_update new_poly theta_for_update last_tv
    (Just _, Just _) -> failTcM $ text "Both inner binds and abs_ev_binds were updated"
  return e {abe_mono = new_mono, abe_poly = new_poly}
  where
    do_mono_update :: TcM (Id, Maybe (ThetaType, TyVar))
    do_mono_update = do
      updates <- readTcRef updateEnv
      case lookupDNameEnv updates (varName mono) of
        Nothing -> return (mono, Nothing)
        Just u -> do
          updTcRef updateEnv (\env -> delFromDNameEnv env (varName mono))
          return (new_id u, Just (new_theta u, last_ty_var u))
    do_poly_update new_poly theta_for_update last_tv = do
      unless (isIdHsWrapper wrap) $ failTcM $ text "Rewrite inside AbsBinds with non-identity abe_wrap"
      let update =
            UInfo
              { old_type = idType poly,
                new_id = new_poly,
                new_theta = theta_for_update,
                last_ty_var = last_tv
              }
      updTcRef updateEnv (\env -> extendDNameEnv env (varName new_poly) update)

rewriteFunBind :: TcRef UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteFunBind updateEnv b@(FunBind {fun_id = (L loc fid), fun_ext = (wrapper, ctick), fun_matches = MG {mg_ext = (MatchGroupTc args res _)}}) = do
  let old_ty = varType fid
  let wrapped = hsWrapperType wrapper $ mkScaledFunTys args res
  let (old_binders, _) = splitPiTys old_ty
  let old_vars = mapMaybe namedBinderVar old_binders
  let w_vars = mapMaybe namedBinderVar $ fst $ splitPiTys wrapped
  let maybe_subst = tcUnifyTys (matchBindFun (mkVarSet w_vars)) (mkTyCoVarTys w_vars) (mkTyCoVarTys old_vars)
  wrapper_res <- removePlaceholdersFromWrapper wrapper
  case (wrapper_res, maybe_subst) of
    (Nothing, _) -> return b
    (_, Nothing) -> failTcM $ text "Failed to unify fun type"
    (Just (wrapper', theta, last_tv), Just subst) -> do
      forM_ old_binders $ \case
        Anon {} -> return ()
        Named bndr
          | isVisibleForAllTyBinder bndr ->
              failTcM $
                text "Adding total constraints to visible foralls is not supported:"
                  $$ ppr old_ty
          | otherwise -> return ()
      let theta' = substTheta subst theta
      last_tv' <- case substTyVar subst last_tv of
        TyVarTy tv -> return tv
        _ -> failTcM $ text "substitution assigned last tv to something other than a tv"
      let rewrapped = substTy subst $ hsWrapperType wrapper' $ mkScaledFunTys args res
      new_ty <- copy_flags old_ty rewrapped
      let fid' = setVarType fid new_ty
      let uinfo = UInfo {new_id = fid', old_type = old_ty, new_theta = theta', last_ty_var = last_tv'}
      updTcRef updateEnv (\env -> extendDNameEnv env (varName fid') uinfo)
      return b {fun_id = L loc fid', fun_ext = (wrapper', ctick)}
  where
    add_flag :: ForAllTyFlag -> State [ForAllTyFlag] ForAllTyFlag
    add_flag flag = modify (flag :) >> return flag

    get_flags :: Type -> [ForAllTyFlag]
    get_flags ty = execState (everywhereM (mkM add_flag) ty) []

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
      let new_flags = get_flags tgt
      unless (length old_flags == length new_flags) $ failTcM $ text "number of foralls changed, bug"
      let (result, remaining_flags) = everywhereM (mkM set_flag) tgt `runState` reverse old_flags
      unless (null remaining_flags) $ error "impossible"
      let set_flags = get_flags result
      unless (old_flags == set_flags) $ failTcM $ text "flag setting failed"
      return result
rewriteFunBind _ b = return b

namedBinderVar :: PiTyBinder -> Maybe TyCoVar
namedBinderVar (Named (Bndr var _)) = Just var
namedBinderVar _ = Nothing

removePlaceholdersFromWrapper :: HsWrapper -> TcM (Maybe (HsWrapper, [PredType], TyVar))
removePlaceholdersFromWrapper wrapper = do
  newArgsRef <- newTcRef []
  wrapper' <- everywhereM (mkM (rewriteWpLet newArgsRef)) wrapper
  tys <- readTcRef newArgsRef
  case tys of
    [] -> return Nothing
    [[]] -> return Nothing
    [new_ev_vars] -> do
      target_tv <- findLastTyLamOfSet (map evVarPred new_ev_vars) wrapper'
      (tv, wrapper'') <- rewriteLastTyLamAfter new_ev_vars target_tv wrapper'
      return $ Just (wrapper'', map evVarPred new_ev_vars, tv)
    _ -> failTcM $ text "encountered multiple zonked WpLet, this should not happen"

rewriteWpLet :: TcRef [[EvVar]] -> HsWrapper -> TcM HsWrapper
rewriteWpLet newArgsRef (WpLet ev_binds) = do
  (ev_vars, ev_binds') <- rewriteTcEvBinds ev_binds
  updTcRef newArgsRef (ev_vars :)
  return $ WpLet ev_binds'
rewriteWpLet _ w = return w

rewriteTcEvBinds :: TcEvBinds -> TcM ([EvVar], TcEvBinds)
rewriteTcEvBinds (TcEvBinds (CoEvBindsVar {})) = failTcM $ text "unexpected CoEvBindsVar"
rewriteTcEvBinds (TcEvBinds (EvBindsVar {ebv_binds = ebv})) = do
  ebm <- readTcRef ebv
  rewriteTcEvBinds (EvBinds (evBindMapBinds ebm))
rewriteTcEvBinds (EvBinds binds) = do
  let (binds', ev_vars) = runState (filterBagM isNotPlaceholder binds) []
  return (ev_vars, EvBinds binds')

isNotPlaceholder :: EvBind -> State [EvVar] Bool
isNotPlaceholder (EvBind {eb_lhs = evVar, eb_rhs = evTerm})
  | isPlaceholder evTerm = do
      modify (evVar :)
      return False
  | otherwise = return True

findLastTyLamOfSet :: [PredType] -> HsWrapper -> TcM TyVar
findLastTyLamOfSet preds w = case go w of
  Nothing -> do
    failTcM (text "Variables appearing in added constraints" <+> ppr preds <+> text "are not bound here")
  Just tv -> return tv
  where
    vars = tyCoVarsOfTypes preds

    go (WpCompose w1 w2) = case go w2 of
      Nothing -> go w1
      Just tv -> Just tv
    go (WpTyLam tv) = if tv `elemVarSet` vars then Just tv else Nothing
    go (WpFun _ w2 _) = go w2
    go _ = Nothing

rewriteLastTyLamAfter :: [EvVar] -> TyVar -> HsWrapper -> TcM (TyVar, HsWrapper)
rewriteLastTyLamAfter ev_vars target_tv w = case go w Nothing of
  Left Nothing -> failTcM (text "Couldn't find the target type var" <+> ppr w)
  Left (Just tv) -> return (tv, w <.> rewrite WpHole)
  Right (tv, w') -> return (tv, w')
  where
    go :: HsWrapper -> Maybe TyVar -> Either (Maybe TyVar) (TyVar, HsWrapper)
    go (WpCompose w1 w2) s = case go w1 s of
      Left s' -> case go w2 s' of
        Left s'' -> Left s''
        Right (tv, w2') -> Right (tv, w1 <.> w2')
      Right (tv, w1') -> Right (tv, w1' <.> w2)
    go (WpTyLam tv) Nothing = if tv == target_tv then Left (Just tv) else Left Nothing
    go (WpTyLam tv) (Just _) = Left (Just tv)
    go (WpFun w1 w2 args) s = case go w2 s of
      Left (Just tv) -> Right (tv, WpFun w1 (w2 <.> rewrite WpHole) args)
      Left s' -> Left s'
      Right (tv, w2') -> Right (tv, WpFun w1 w2' args)
    go _ Nothing = Left Nothing
    go w' (Just tv) = Right (tv, rewrite w')

    rewrite w' = foldr ((<.>) . WpEvLam) w' ev_vars
