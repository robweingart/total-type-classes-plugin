{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module TotalClassPlugin.Rewriter.Call (rewriteCalls) where

import Control.Monad (unless, when, forM, forM_)
import Data.Generics (Data (gmapM), GenericM, everything, extM, mkQ)
import Data.Maybe (isJust)
import GHC (GhcTc, HsExpr (..), HsWrap (HsWrap), LHsBind, LHsBinds, LHsExpr, XXExprGhcTc (..), mkHsWrap, LPat, LMatch)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.Subst (elemSubst)
import GHC.Data.Bag (emptyBag)
import GHC.Hs.Syn.Type (hsExprType, lhsExprType)
import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Solver (captureTopConstraints, simplifyTop)
import GHC.Tc.Types (TcGblEnv (..), TcLclEnv, TcM)
import GHC.Tc.Types.Evidence (EvBind (eb_rhs), EvBindsVar (CoEvBindsVar, EvBindsVar, ebv_binds), HsWrapper (..), TcEvBinds (EvBinds, TcEvBinds), evBindMapBinds, mkWpLet, (<.>))
import GHC.Tc.Types.Origin (CtOrigin (ExprSigOrigin, OccurrenceOf))
import GHC.Tc.Utils.Instantiate (instCallConstraints)
import GHC.Tc.Utils.Monad (addTopEvBinds, getEnvs, readTcRef, restoreEnvs, setGblEnv, wrapLocFstMA, wrapLocMA)
import GHC.Tc.Utils.TcType (TcThetaType)
import TotalClassPlugin.GHCUtils (hsWrapperTypeSubst, piResultTysSubst)
import TotalClassPlugin.Rewriter.Bind (removePlaceholdersFromWrapper)
import TotalClassPlugin.Rewriter.Capture
import TotalClassPlugin.Rewriter.Env
import TotalClassPlugin.Rewriter.Placeholder (isPlaceholder)
import TotalClassPlugin.Rewriter.Utils
import TotalClassPlugin.Rewriter.Validate (checkNoPlaceholders)

rewriteCalls :: UpdateEnv -> LHsBinds GhcTc -> (LHsBinds GhcTc -> TcM (TcGblEnv, TcLclEnv)) -> TcM (TcGblEnv, TcLclEnv)
rewriteCalls ids binds cont
  | isEmptyDNameEnv ids = do
      printLnTcM "No new modified ids, checking for remaining placeholders"
      checkNoPlaceholders binds
      getEnvs
  | otherwise = do
      -- forM_ ids $ outputTcM ""
      (binds', lie) <- captureTopConstraints $ rewriteCallsIn ids binds
      (gbl, lcl) <- getEnvs
      new_ev_binds <- restoreEnvs (gbl, lcl) $ simplifyTop lie
      when (any (isPlaceholder . eb_rhs) new_ev_binds) $ failTcM $ text "Placeholder leaked into global constraints" <+> ppr new_ev_binds
      binds'' <- rezonkAllTcEvBinds binds'
      when (everything (||) (mkQ False (\case TcEvBinds _ -> True; _ -> False)) binds'') $ failTcM $ text "TcEvBinds var survived rezonking"
      setGblEnv gbl {tcg_binds = binds''} $ addTopEvBinds new_ev_binds $ do
        cont binds''

rezonkAllTcEvBinds :: GenericM TcM
rezonkAllTcEvBinds =
  gmapM rezonkAllTcEvBinds
    `extM` rezonkWpLet
    `extM` rezonkTcEvBinds

rezonkWpLet :: HsWrapper -> TcM HsWrapper
rezonkWpLet (WpCompose w1 w2) = liftA2 (<.>) (rezonkWpLet w1) (rezonkWpLet w2)
rezonkWpLet (WpLet ev_binds) = mkWpLet <$> rezonkTcEvBinds ev_binds
rezonkWpLet w = return w

rezonkTcEvBinds :: TcEvBinds -> TcM TcEvBinds
rezonkTcEvBinds (TcEvBinds (CoEvBindsVar {})) = return $ EvBinds emptyBag
rezonkTcEvBinds (TcEvBinds (EvBindsVar {ebv_binds = var})) = do
  ebm <- readTcRef var
  return $ EvBinds $ evBindMapBinds ebm
rezonkTcEvBinds (EvBinds ebs) = return $ EvBinds ebs

rewriteCallsIn :: UpdateEnv -> GenericM TcM
rewriteCallsIn ids =
  gmapM (rewriteCallsIn ids)
    `extM` (wrapLocMA (rewriteWrapExpr ids (rewriteCallsIn ids)) :: LHsExpr GhcTc -> TcM (LHsExpr GhcTc))
    `extM` (wrapLocMA (captureAndUpdateMatch (rewriteCallsIn ids)) :: LMatch GhcTc (LHsExpr GhcTc) -> TcM (LMatch GhcTc (LHsExpr GhcTc)))
    `extM` (wrapLocMA (captureAndUpdateBind (rewriteCallsIn ids)) :: LHsBind GhcTc -> TcM (LHsBind GhcTc))

data UpdateToApply = UpdateToApply {uta_origin :: CtOrigin, uta_new_theta :: TcThetaType, uta_last_ty_var :: TyVar}

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
      -- outputFullTcM "go_outer " outer
      let old_ty = hsExprType outer
      (expr', maybe_update) <- go outer
      let new_ty = hsExprType expr'
      case (old_ty `eqType` new_ty, maybe_update) of
        (False, Nothing) -> failTcM $ text "no update but inner type changed " <+> ppr new_ty
        (_, Just ((UpdateToApply{uta_new_theta=theta}), _)) -> do
          failTcM $ text "Failed to insert added constraints" <+> ppr theta <+> text "into" <+> ppr outer
        (True, Nothing) -> return expr'

    go :: HsExpr GhcTc -> TcM (HsExpr GhcTc, Maybe (UpdateToApply, Subst))
    go expr@(XExpr (WrapExpr (HsWrap wrap old_inner))) = do
      let (tvs, evs) = wrapperLams wrap
      (ev_binds, (new_inner, update_result)) <- captureConstraints tvs evs $ do
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
      let new_type_for_checking = hsExprType (XExpr (WrapExpr (HsWrap new_wrap new_inner)))
      unless (isJust remaining_update || hsExprType expr `eqType` new_type_for_checking) $
        failTcM $
          text "Type still different after update:"
            <+> ( vcat $
                    [ text "old:" <+> ppr (hsExprType expr),
                      text "new:" <+> ppr new_type_for_checking
                    ]
                )
      remove_placeholders_result <- removePlaceholdersFromWrapper new_wrap
      (final_wrap, maybe_update) <- case (remove_placeholders_result, remaining_update) of
        (Nothing, maybe_update) -> return (new_wrap, maybe_update)
        (Just _, Just _) -> failTcM $ text "two updates?"
        (Just (final_wrap, added_theta, last_tv), Nothing) -> return (final_wrap, Just (UpdateToApply {uta_origin = ExprSigOrigin, uta_new_theta = added_theta, uta_last_ty_var = last_tv}, emptySubst))
      let new_expr = XExpr (WrapExpr (HsWrap final_wrap new_inner))
      -- outputTcM "subst" (snd <$> maybe_update)
      return (new_expr, maybe_update)
    go (HsAppType ty old_inner tok wc_type) = do
      (new_inner, maybe_update) <- wrapLocFstMA go old_inner
      let subst = snd $ piResultTysSubst (lhsExprType old_inner) [ty]
      let new_expr = HsAppType ty new_inner tok wc_type
      mk_ev_apps_for_update subst maybe_update >>= \case
        Left remaining_update -> return (new_expr, Just remaining_update)
        Right new_ev_apps -> return (mkHsWrap new_ev_apps new_expr, Nothing)
    go (HsPar x l_tok old_inner r_tok) = do
      (new_inner, maybe_update) <- wrapLocFstMA go old_inner
      return (HsPar x l_tok new_inner r_tok, maybe_update)
    go (HsVar x (L l var))
      | Just update <- lookupDNameEnv updates $ varName var = do
          let new_ty = idType (new_id update)
          -- outputTcM "starting update: " update
          return ((HsVar x (L l (setVarType var new_ty))), Just (UpdateToApply {uta_origin = OccurrenceOf (varName var), uta_new_theta = new_theta update, uta_last_ty_var = last_ty_var update}, emptySubst))
    go (HsApp x f arg) = do
      (new_f, f_update) <- wrapLocFstMA go f
      (new_arg, arg_update) <- wrapLocFstMA go arg
      maybe_update <- case (f_update, arg_update) of
        (Nothing, Nothing) -> return Nothing
        (Just update, Nothing) -> return (Just update)
        (Nothing, Just update) -> do
          outputTcM "Update from argument: " arg
          return (Just update)
        (Just _, Just _) -> failTcM $ text "Modified both function and argument of this call"
      return (HsApp x new_f new_arg, maybe_update)
    go (ExprWithTySig x old_inner sig) = do
      (new_inner, maybe_update) <- wrapLocFstMA go old_inner
      return (ExprWithTySig x new_inner sig, maybe_update)
    go expr = do
      expr' <- inside expr
      unless (hsExprType expr `eqType` hsExprType expr') $
        failTcM $
          text "Inner type is not a changed id, but its type changed " <+> ppr expr'
      return (expr', Nothing)

mk_ev_apps :: Subst -> UpdateToApply -> TcM HsWrapper
mk_ev_apps subst update = do
  let vars = tyCoVarsOfTypes (uta_new_theta update)
  let unassigned_vars = filterVarSet (`notElemSubst` subst) vars
  unless (isEmptyVarSet unassigned_vars) $ failTcM $ text "the following vars from the called function's type have not been applied at this insertion point:" <+> ppr unassigned_vars
  let theta = substTheta subst (uta_new_theta update)
  -- outputTcM "Emitting constraints: " theta
  instCallConstraints (uta_origin update) theta

mk_ev_apps_for_update :: Subst -> Maybe (UpdateToApply, Subst) -> TcM (Either (UpdateToApply, Subst) HsWrapper)
mk_ev_apps_for_update _ Nothing = return $ Right WpHole
mk_ev_apps_for_update new_subst (Just (update, old_subst))
  | elemSubst (uta_last_ty_var update) subst = do
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
