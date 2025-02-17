{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}

module TotalClassPlugin.Rewriter.Call (rewriteCalls) where

import GHC.Plugins hiding (TcPlugin)
import GHC (HsBindLR(..), GhcTc, HsExpr(..), XXExprGhcTc(..), HsWrap (HsWrap), LHsBind, LHsExpr, LHsBinds, HsBind, AbsBinds (abs_tvs, abs_ev_vars, abs_ev_binds, abs_binds, AbsBinds, abs_exports, abs_sig), mkHsWrap)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcLclEnv)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (eb_rhs), TcEvBinds (TcEvBinds, EvBinds), evBindMapBinds, EvBindsVar (ebv_binds, EvBindsVar, CoEvBindsVar), mkWpLet, extendEvBinds, emptyTcEvBinds)
import Data.Generics (mkQ, GenericM, Data (gmapM), everything, extM)
import GHC.Hs.Syn.Type (hsExprType)
import GHC.Tc.Utils.Monad (readTcRef, updTcRef, wrapLocMA, getEnvs, restoreEnvs, setGblEnv, addTopEvBinds, setSrcSpanA, wrapLocFstMA)
import GHC.Tc.Utils.Instantiate (instCallConstraints)
import GHC.Tc.Types.Origin (CtOrigin(OccurrenceOf), SkolemInfoAnon (UnkSkol))

import TotalClassPlugin.Rewriter.Env
import TotalClassPlugin.Rewriter.Utils
import GHC.Core.TyCo.Compare (eqType)
import Control.Monad (unless, when)
import GHC.Core.TyCo.Subst (elemSubst)
import GHC.Tc.Utils.Unify (checkConstraints)
import GHC.Tc.Utils.Env (tcExtendNameTyVarEnv)
import GHC.Tc.Utils.TcType (mkTyVarNamePairs)
import GHC.Data.Bag (unionBags, emptyBag)
import GHC.Tc.Solver (captureTopConstraints, simplifyTop)
import GHC.Stack (emptyCallStack)
import Data.Maybe (isJust)
import TotalClassPlugin.Rewriter.Placeholder (isPlaceholder)
import TotalClassPlugin.GHCUtils (hsWrapperTypeSubst, piResultTysSubst)

rewriteCalls :: UpdateEnv -> LHsBinds GhcTc -> (LHsBinds GhcTc -> TcM (TcGblEnv, TcLclEnv)) -> TcM (TcGblEnv, TcLclEnv)
rewriteCalls ids binds cont
  | isEmptyDNameEnv ids = do
    printLnTcM "No new modified ids, ending loop"
    getEnvs
  | otherwise = do
    -- forM_ ids (outputTcM "")
    (binds', lie) <- captureTopConstraints $ rewriteCallsIn ids binds
    (gbl, lcl) <- getEnvs
    new_ev_binds <- restoreEnvs (gbl, lcl) $ simplifyTop lie
    when (any (isPlaceholder . eb_rhs) new_ev_binds) $ failTcM $ text "Placeholder leaked into global constraints" <+> ppr new_ev_binds
    binds'' <- rezonkAllTcEvBinds binds'
    when (everything (||) (mkQ False (\case { TcEvBinds _ -> True; _ -> False })) binds'') $ failTcM $ text "TcEvBinds var survived rezonking"
    setGblEnv gbl{tcg_binds=binds''} $ addTopEvBinds new_ev_binds $ do
      cont binds''

rezonkAllTcEvBinds :: GenericM TcM
rezonkAllTcEvBinds = gmapM rezonkAllTcEvBinds
                     `extM` rezonkWpLet
                     `extM` rezonkTcEvBinds

rezonkWpLet :: HsWrapper -> TcM HsWrapper
rezonkWpLet (WpCompose w1 w2) = liftA2 (<.>) (rezonkWpLet w1) (rezonkWpLet w2)
rezonkWpLet (WpLet ev_binds) = mkWpLet <$> rezonkTcEvBinds ev_binds
rezonkWpLet w = return w

rezonkTcEvBinds :: TcEvBinds -> TcM TcEvBinds
rezonkTcEvBinds (TcEvBinds (CoEvBindsVar{})) = return $ EvBinds emptyBag
rezonkTcEvBinds (TcEvBinds (EvBindsVar{ebv_binds=var})) = do
  ebm <- readTcRef var
  return $ EvBinds $ evBindMapBinds ebm
rezonkTcEvBinds (EvBinds ebs) = return $ EvBinds ebs

reskolemise :: [TyVar] -> [EvVar] -> TcM result -> TcM (TcEvBinds, result)
reskolemise [] [] thing_inside = do
  res <- thing_inside
  return (emptyTcEvBinds, res)
reskolemise tvs given thing_inside = do
  (new_ev_binds, result) <- 
    checkConstraints (UnkSkol emptyCallStack) tvs given $
    tcExtendNameTyVarEnv (mkTyVarNamePairs tvs) $
    thing_inside
  return (new_ev_binds, result)

addToWpLet :: TcEvBinds -> HsWrapper -> TcM HsWrapper 
addToWpLet new_ev_binds wrap = do
  withTcRef (0 :: Int) (go wrap) >>= \case
    (0, wrap') -> return $ wrap' <.> mkWpLet new_ev_binds
    (1, wrap') -> return wrap'
    _ -> failTcM $ text "Too many WpLet"
  where
    go WpHole _ = return WpHole
    go (WpCompose w1 w2) counter = liftA2 (<.>) (go w1 counter) (go w2 counter)
    go (WpLet ev_binds) counter = do
      updTcRef counter (+1)
      mkWpLet <$> addToTcEvBinds ev_binds new_ev_binds
    go w _ = return w

addToTcEvBinds :: TcEvBinds -> TcEvBinds -> TcM TcEvBinds
addToTcEvBinds (TcEvBinds _) _ = failTcM $ text "Encountered unzonked TcEvBinds, this should not happen"
addToTcEvBinds (EvBinds binds) new_ev_binds = case new_ev_binds of
  TcEvBinds (EvBindsVar{ebv_binds=binds_ref}) -> do
    updTcRef binds_ref (\ebm -> foldr (flip extendEvBinds) ebm binds)
    return new_ev_binds
  TcEvBinds (CoEvBindsVar{}) -> failTcM $ text "Added CoEvBindsVar to existing WpLet"
  EvBinds new_binds -> return $ EvBinds (new_binds `unionBags` binds)

wrapperLams :: HsWrapper -> ([TyVar], [EvVar])
wrapperLams w = go w ([], [])
  where
    go :: HsWrapper -> ([TyVar], [EvVar]) -> ([TyVar], [EvVar])
    go WpHole vs = vs
    go (WpCompose w1 w2) vs = go w1 $ go w2 vs 
    go (WpFun _ w2 _) vs = go w2 vs
    go (WpTyLam tv) (tvs, evs) = (tv : tvs, evs)
    go (WpEvLam ev) (tvs, evs) = (tvs, ev : evs)
    go _ vs = vs

rewriteCallsIn :: UpdateEnv -> GenericM TcM
rewriteCallsIn ids = gmapM (rewriteCallsIn ids)
                     `extM` (wrapLocMA (rewriteWrapExpr ids (rewriteCallsIn ids)) :: LHsExpr GhcTc -> TcM (LHsExpr GhcTc))
                     `extM` (wrapLocMA (rewriteHsBind (rewriteCallsIn ids)) :: LHsBind GhcTc -> TcM (LHsBind GhcTc))

rewriteHsBind :: GenericM TcM -> HsBind GhcTc -> TcM (HsBind GhcTc)
rewriteHsBind inside b = do
  (maybe_ev_binds, b') <- reskolemiseBind b $ gmapM inside b
  case maybe_ev_binds of
    Nothing -> return b'
    Just ev_binds -> insertTcEvBinds ev_binds b'

reskolemiseBind :: HsBind GhcTc -> TcM result -> TcM (Maybe TcEvBinds, result)
reskolemiseBind (FunBind {fun_ext=(wrap, _)}) thing_inside = do
  let (tvs, evs) = wrapperLams wrap
  (binds, result) <- reskolemise tvs evs $ thing_inside
  return (Just binds, result)
reskolemiseBind (XHsBindsLR (AbsBinds { abs_tvs=tvs, abs_ev_vars=evs })) thing_inside = do
  (binds, result) <- reskolemise tvs evs $ thing_inside
  return (Just binds, result)
reskolemiseBind _ thing_inside = do
  result <- thing_inside
  return (Nothing, result)


insertTcEvBinds :: TcEvBinds -> HsBind GhcTc -> TcM (HsBind GhcTc)
insertTcEvBinds new_ev_binds b@(FunBind {fun_ext=(wrap, ctick)}) = do
  wrap' <- addToWpLet new_ev_binds wrap
  return $ b{fun_ext=(wrap', ctick)}
insertTcEvBinds new_ev_binds (XHsBindsLR (AbsBinds { abs_tvs=tvs
                                          , abs_ev_vars=ev_vars
                                          , abs_exports=exports
                                          , abs_ev_binds=ev_binds
                                          , abs_binds=binds
                                          , abs_sig=sig })) = do
  ev_binds' <- case ev_binds of
    [] -> return [new_ev_binds]
    [old_ev_binds] -> do
      combined <- addToTcEvBinds old_ev_binds new_ev_binds
      return [combined]
    [dfun_ev_binds, local_ev_binds] -> do
      local_ev_binds' <- addToTcEvBinds local_ev_binds new_ev_binds
      return [dfun_ev_binds, local_ev_binds']
    _ -> failTcM $ text "Reskolemised AbsBinds with more than two abs_ev_binds"
  return $ XHsBindsLR (AbsBinds { abs_tvs=tvs
                                       , abs_ev_vars=ev_vars
                                       , abs_exports=exports
                                       , abs_ev_binds=ev_binds'
                                       , abs_binds=binds
                                       , abs_sig=sig })
insertTcEvBinds _ b = failTcM $ text "Can't add TcEvBinds to this kind of HsBind: " <+> ppr b


rewriteWrapExpr :: UpdateEnv -> GenericM TcM -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteWrapExpr updates inside outer = do
  case outer of
    (XExpr (WrapExpr _)) -> go_outer
    (HsAppType _ _ _ _) -> go_outer
    (HsVar _ (L _ var))
      | Just _ <- lookupDNameEnv updates (varName var) -> failTcM $ text "call to modified function " <+> ppr outer <+> text " is not immediate child of a wrapper"
    _ -> gmapM inside outer
  where
    go_outer = do
      let old_ty = hsExprType outer
      (expr', maybe_update) <- go outer
      let new_ty = hsExprType expr'
      case (old_ty `eqType` new_ty, maybe_update) of
        (False, Nothing) -> failTcM $ text "no update but inner type changed " <+> ppr new_ty
        (_, Just _) -> failTcM $ text "update not resolved"
        (True, Nothing) -> return expr'

    go :: HsExpr GhcTc -> TcM (HsExpr GhcTc, Maybe (UpdateInfo, Subst))
    go expr@(XExpr (WrapExpr (HsWrap wrap old_inner))) = do 
      let (tvs, evs) = wrapperLams wrap
      (ev_binds, (new_inner, update_result)) <- reskolemise tvs evs $ do 
        (new_inner, maybe_update) <- go old_inner
        let subst = snd $ hsWrapperTypeSubst wrap (hsExprType old_inner)
        update_result <- mk_ev_apps_for_update subst maybe_update
        return (new_inner, update_result)
      wrap_with_ev_binds <- addToWpLet ev_binds wrap
      (new_wrap, remaining_update) <- case update_result of
        Left remaining_update -> return (wrap_with_ev_binds, Just remaining_update)
        Right new_ev_apps -> do
          updated_wrap <- maybe_add_to_first_ty_app wrap_with_ev_binds new_ev_apps
          return (updated_wrap, Nothing)
      let new_expr = XExpr (WrapExpr (HsWrap new_wrap new_inner))
      unless (isJust remaining_update || hsExprType expr `eqType` hsExprType new_expr) $
        failTcM $ text "Type still different after update:" <+> (vcat $
          [ text "old:" <+> ppr (hsExprType expr)
          , text "new:" <+> ppr (hsExprType new_expr)
          ])
      return (new_expr, remaining_update)
    go (HsAppType ty old_inner tok wc_type) = do
      (new_inner, maybe_update) <- wrapLocFstMA go old_inner
      let subst = snd $ piResultTysSubst (hsExprType (unLoc old_inner)) [ty]
      let new_expr = HsAppType ty new_inner tok wc_type
      mk_ev_apps_for_update subst maybe_update >>= \case
        Left remaining_update -> return (new_expr, Just remaining_update)
        Right new_ev_apps -> return (mkHsWrap new_ev_apps new_expr, Nothing)
    go (HsPar x l_tok old_inner r_tok) =do
      (new_inner, maybe_update) <- wrapLocFstMA go old_inner
      return (HsPar x l_tok new_inner r_tok, maybe_update)
    go (HsVar x (L l var))
      | Just update <- lookupDNameEnv updates $ varName var = do
        return ((HsVar x (L l (new_id update))), Just (update, emptySubst))
    go (HsApp x f arg) = do
      (new_f, maybe_update) <- wrapLocFstMA go f
      return (HsApp x new_f arg, maybe_update)
    go expr = do
      expr' <- inside expr
      unless (hsExprType expr `eqType` hsExprType expr') $
        failTcM $ text "Inner type is not a changed id, but its type changed " <+> ppr expr'
      return (expr', Nothing)

mk_ev_apps :: Subst -> UpdateInfo -> TcM HsWrapper
mk_ev_apps subst update = do
  let vars = tyCoVarsOfTypes (new_theta update)
  let unassigned_vars = filterVarSet (`notElemSubst` subst) vars
  unless (isEmptyVarSet unassigned_vars) $ failTcM $ text "the following vars from the called function's type have not been applied at this insertion point:" <+> ppr unassigned_vars 
  let theta = substTheta subst (new_theta update)
  -- outputTcM "Emitting constraints: " theta
  instCallConstraints (OccurrenceOf $ varName $ new_id update) theta

mk_ev_apps_for_update :: Subst -> Maybe (UpdateInfo, Subst) -> TcM (Either (UpdateInfo, Subst) HsWrapper)
mk_ev_apps_for_update _ Nothing = return $ Right WpHole
mk_ev_apps_for_update new_subst (Just (update, old_subst))
  | elemSubst (last_ty_var update) subst = do
    new_ev_apps <- mk_ev_apps subst update
    -- outputTcM "Successfully applied " (update, subst)
    -- printWrapper 1 new_ev_apps
    return $ Right new_ev_apps
  | otherwise = return $ Left (update, subst)
  where
    subst = unionSubst new_subst old_subst

maybe_add_to_first_ty_app :: HsWrapper -> HsWrapper -> TcM HsWrapper
maybe_add_to_first_ty_app wrap WpHole = return wrap
maybe_add_to_first_ty_app wrap new_wrap = case go wrap of
  Nothing -> failTcM $ text "Couldn't find WpTyApp in call site wrapper"
  Just wrap' -> return wrap'
  where
    go (WpCompose w1 w2) = case go w1 of
      Nothing -> fmap (w1 <.>) $ go w2
      Just w1' -> Just (w1' <.> w2)
    go w@(WpTyApp _) = Just (new_wrap <.> w)
    go _ = Nothing

