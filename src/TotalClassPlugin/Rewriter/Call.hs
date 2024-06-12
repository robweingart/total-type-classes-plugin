{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}

module TotalClassPlugin.Rewriter.Call (rewriteCalls) where

import GHC.Plugins hiding (TcPlugin)
import GHC (HsBindLR(..), GhcTc, HsExpr(..), XXExprGhcTc(..), HsWrap (HsWrap), LHsBind, LHsExpr, LHsBinds, HsBind, SrcSpanAnn', AbsBinds (abs_tvs, abs_ev_vars, abs_ev_binds, abs_binds, AbsBinds, abs_exports, abs_sig), mkHsWrap)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcLclEnv)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (eb_rhs), TcEvBinds (TcEvBinds, EvBinds), evBindMapBinds, EvBindsVar (ebv_binds, EvBindsVar, CoEvBindsVar), mkWpLet, extendEvBinds, emptyTcEvBinds)
import Data.Generics (mkM, mkQ, GenericM, Data (gmapM), everything)
import GHC.Hs.Syn.Type (hsExprType)
import GHC.Tc.Utils.Monad (readTcRef, updTcRef, wrapLocMA, getEnvs, restoreEnvs, setGblEnv, addTopEvBinds, setSrcSpanA)
import GHC.Tc.Utils.Instantiate (instCallConstraints)
import GHC.Tc.Types.Origin (CtOrigin(OccurrenceOf), SkolemInfoAnon (UnkSkol))

import TotalClassPlugin.Rewriter.Env
import TotalClassPlugin.Rewriter.Utils
import GHC.Core.TyCo.Compare (eqType)
import Control.Monad (unless, forM_, when)
import GHC.Core.TyCo.Subst (elemSubst)
import GHC.Tc.Utils.Unify (checkConstraints)
import GHC.Tc.Utils.Env (tcExtendNameTyVarEnv)
import GHC.Tc.Utils.TcType (mkTyVarNamePairs)
import GHC.Data.Bag (Bag, unionBags, emptyBag)
import GHC.Tc.Solver (captureTopConstraints, simplifyTop)
import GHC.Stack (emptyCallStack)
import Data.Maybe (isJust)
import TotalClassPlugin.Rewriter.Placeholder (isPlaceholder)

rewriteCalls :: UpdateEnv -> LHsBinds GhcTc -> (LHsBinds GhcTc -> TcM (TcGblEnv, TcLclEnv)) -> TcM (TcGblEnv, TcLclEnv)
rewriteCalls ids binds cont
  | isEmptyDNameEnv ids = do
    printLnTcM "No new modified ids, ending loop"
    --outputFullTcM "Full at end: " binds
    getEnvs
  | otherwise = do
    --outputFullTcM "Full before rewriteCalls: " binds
    forM_ ids (outputTcM "")
    (binds', lie) <- captureTopConstraints $ rewriteCallsIn ids binds
    --outputTcM "Captured constraints:" lie
    (gbl, lcl) <- getEnvs
    new_ev_binds <- restoreEnvs (gbl, lcl) $ simplifyTop lie
    when (any (isPlaceholder . eb_rhs) new_ev_binds) $ failTcM $ text "Placeholder leaked into global constraints" <+> ppr new_ev_binds
    binds'' <- rezonkAllTcEvBinds binds'
    when (everything (||) (mkQ False (\case { TcEvBinds _ -> True; _ -> False })) binds'') $ failTcM $ text "TcEvBinds var survived rezonking"
    setGblEnv gbl{tcg_binds=binds''} $ addTopEvBinds new_ev_binds $ do
      cont binds''

rezonkAllTcEvBinds :: GenericM TcM
rezonkAllTcEvBinds x = orElseM (mkMMaybe (fmap Just . rezonkWpLet) x)  $
                       orElseM (mkMMaybe (fmap (Just . EvBinds) . rezonkTcEvBinds) x) $
                       gmapM rezonkAllTcEvBinds x

rezonkWpLet :: HsWrapper -> TcM HsWrapper
rezonkWpLet (WpCompose w1 w2) = liftA2 (<.>) (rezonkWpLet w1) (rezonkWpLet w2)
rezonkWpLet (WpLet ev_binds) = (mkWpLet . EvBinds) <$> rezonkTcEvBinds ev_binds
rezonkWpLet w = return w

rezonkTcEvBinds :: TcEvBinds -> TcM (Bag EvBind)
rezonkTcEvBinds (TcEvBinds (CoEvBindsVar{})) = return emptyBag
rezonkTcEvBinds (TcEvBinds (EvBindsVar{ebv_binds=var})) = evBindMapBinds <$> readTcRef var
rezonkTcEvBinds (EvBinds ebs) = return ebs

reskolemise :: [TyVar] -> [EvVar] -> TcM result -> TcM (TcEvBinds, result)
reskolemise [] [] thing_inside = do
    res <- thing_inside
    return (emptyTcEvBinds, res)
reskolemise tvs given thing_inside = do
    printLnTcM "reskolemise {"
    (new_ev_binds, result) <- 
      checkConstraints (UnkSkol emptyCallStack) tvs given $
      tcExtendNameTyVarEnv (mkTyVarNamePairs tvs) $
      thing_inside
    outputTcM "} New ev binds:" new_ev_binds
    return (new_ev_binds, result)

reskolemiseWrapper :: HsWrapper -> TcM result -> TcM (HsWrapper, result)
reskolemiseWrapper WpHole thing_inside = do
  result <- thing_inside
  return (WpHole, result)
reskolemiseWrapper wrap thing_inside = do
  printLnTcM "reskolemiseWrapper {"
  (tvs, given) <- wrapperLams wrap
  printWrapper 1 wrap
  (new_ev_binds, result) <- reskolemise tvs given thing_inside
  new_wrap <- addToWpLet new_ev_binds wrap
  printLnTcM "} New wrapper:"
  printWrapper 1 new_wrap
  return (new_wrap, result)

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

wrapperLams :: HsWrapper -> TcM ([TyVar], [EvVar])
wrapperLams w = go w ([], [])
  where
    go :: HsWrapper -> ([TyVar], [EvVar]) -> TcM ([TyVar], [EvVar])
    go WpHole vs = return vs
    go (WpCompose w1 w2) vs = go w2 vs >>= go w1
    go (WpFun _ w2 _) vs = go w2 vs
    go (WpTyLam tv) (tvs, evs) = return (tv : tvs, evs)
    go (WpEvLam ev) (tvs, evs) = return (tvs, ev : evs)
    go _ vs = return vs

rewriteCallsIn :: UpdateEnv -> GenericM TcM
rewriteCallsIn ids x = orElseM (mkMMaybe (rewriteLHsBind ids) x) $
                       orElseM (mkMMaybe (rewriteLWrapExpr ids) x) $
                       (mkM (noRewriteLVar ids) x >>= gmapM (rewriteCallsIn ids))

noRewriteLVar :: UpdateEnv -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
noRewriteLVar updates = wrapLocMA (noRewriteVar updates)

noRewriteVar :: UpdateEnv -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
noRewriteVar updates expr@(HsVar _ (L _ var))
  | Just _ <- lookupDNameEnv updates (varName var) = failTcM $ text "call to modified function " <+> ppr expr <+> text " is not immediate child of a wrapper"
  | otherwise = do
    outputTcM "noRewriteVar unique: " $ varUnique var
    outputTcM "noRewriteVar updates: " updates
    outputTcM "noRewriteVar ok: " expr
    return expr
noRewriteVar _ expr = do
  return expr

wrapLocMMaybeA :: (a -> TcM (Maybe b)) -> GenLocated (SrcSpanAnn' ann) a -> TcM (Maybe (GenLocated (SrcSpanAnn' ann) b))
wrapLocMMaybeA fn (L loc a) = setSrcSpanA loc $ do 
  b <- fn a
  return $ (L loc) <$> b 

rewriteLHsBind :: UpdateEnv -> LHsBind GhcTc -> TcM (Maybe (LHsBind GhcTc))
rewriteLHsBind updates = wrapLocMMaybeA (rewriteHsBind updates)

rewriteHsBind :: UpdateEnv -> HsBind GhcTc -> TcM (Maybe (HsBind GhcTc))
rewriteHsBind ids b@(FunBind {fun_matches=matches, fun_ext=(wrap, ctick)}) = do
  printLnTcM "rewriteHsBind (FunBind) {"
  outputTcM "Rewriting calls in bind: " b
  --outputTcM "Wraps: " $ snd $ runState (everywhereM (mkM recordXExpr) matches) []
  (wrap', matches') <- reskolemiseWrapper wrap $ rewriteCallsIn ids matches
  printLnTcM "}"
  return $ Just b{fun_matches=matches', fun_ext=(wrap', ctick)}
rewriteHsBind ids b@(XHsBindsLR (AbsBinds { abs_tvs=tvs
                                          , abs_ev_vars=ev_vars
                                          , abs_exports=exports
                                          , abs_ev_binds=ev_binds
                                          , abs_binds=binds
                                          , abs_sig=sig })) = do
  printLnTcM "rewriteHsBind (AbsBinds) {"
  outputTcM "Rewriting calls in bind: " b
  (new_ev_binds, binds') <- reskolemise tvs ev_vars $ mapM (orReturn (rewriteLHsBind ids)) binds
  ev_binds' <- case ev_binds of
    [] -> return [new_ev_binds]
    [old_ev_binds] -> do
      combined <- addToTcEvBinds old_ev_binds new_ev_binds
      return [combined]
    [dfun_ev_binds, local_ev_binds] -> do
      local_ev_binds' <- addToTcEvBinds local_ev_binds new_ev_binds
      return [dfun_ev_binds, local_ev_binds']
    _ -> failTcM $ text "Reskolemised AbsBinds with more than two abs_ev_binds"
  printLnTcM "}"
  return $ Just $ XHsBindsLR (AbsBinds { abs_tvs=tvs
                                       , abs_ev_vars=ev_vars
                                       , abs_exports=exports
                                       , abs_ev_binds=ev_binds'
                                       , abs_binds=binds'
                                       , abs_sig=sig })
  
rewriteHsBind _ _ = return Nothing


rewriteLWrapExpr :: UpdateEnv -> LHsExpr GhcTc -> TcM (Maybe (LHsExpr GhcTc))
rewriteLWrapExpr updates = wrapLocMMaybeA (rewriteWrapExpr updates)

rewriteWrapExpr :: UpdateEnv -> HsExpr GhcTc -> TcM (Maybe (HsExpr GhcTc))
rewriteWrapExpr updates outer = do
  case outer of
    (XExpr (WrapExpr _)) -> go_outer
    (HsAppType _ _ _ _) -> go_outer
    _ -> return Nothing
  where
    go_outer = do
      outputFullTcM "Inspecting wrapped expression {" outer
      let old_ty = hsExprType outer
      (expr', maybe_update) <- go outer
      let new_ty = hsExprType expr'
      case (old_ty `eqType` new_ty, maybe_update) of
        (False, Nothing) -> failTcM $ text "no update but inner type changed " <+> ppr new_ty
        (_, Just _) -> failTcM $ text "update not resolved"
        (True, Nothing) -> do
          printLnTcM "}"
          return $ Just expr'

    go :: HsExpr GhcTc -> TcM (HsExpr GhcTc, Maybe (UpdateInfo, Subst))
    go expr@(XExpr (WrapExpr (HsWrap wrap old_inner))) = do 
      outputTcM "XExpr WrapExpr { " expr 
      (wrap', (new_ev_apps, new_inner, maybe_update)) <- reskolemiseWrapper wrap $ do 
        (new_inner, maybe_update) <- go old_inner
        let subst = snd $ hsWrapperTypeSubst wrap (hsExprType old_inner)
        outputTcM "WrapExpr subst: " subst
        (new_ev_apps, maybe_update') <- maybe_mk_new subst maybe_update
        return (new_ev_apps, new_inner, maybe_update')
      let new_wrap = new_ev_apps <.> wrap'
      let new_expr = XExpr (WrapExpr (HsWrap new_wrap new_inner))
      unless (isJust maybe_update || hsExprType expr `eqType` hsExprType new_expr) $
        failTcM $ text "Type still different after update:" <+> (vcat $
          [ text "old:" <+> ppr (hsExprType expr)
          , text "new:" <+> ppr (hsExprType new_expr)
          ])
      printLnTcM "}"
      return (new_expr, maybe_update)
    go expr@(HsAppType ty (L loc old_inner) tok wc_type) = setSrcSpanA loc $ do
      outputTcM "HsAppType { " expr 
      (new_inner, maybe_update) <- go old_inner
      let subst = snd $ piResultTysSubst (hsExprType old_inner) [ty]
      outputTcM "HsAppType subst: " subst
      (new_ev_apps, maybe_update') <- maybe_mk_new subst maybe_update
      printLnTcM "}"
      return (mkHsWrap new_ev_apps $ HsAppType ty (L loc new_inner) tok wc_type, maybe_update')
    go expr@(HsPar x l_tok (L loc old_inner) r_tok) = setSrcSpanA loc $ do
      outputTcM "HsPar { " expr 
      (new_inner, maybe_update) <- go old_inner
      printLnTcM "}"
      return (HsPar x l_tok (L loc new_inner) r_tok, maybe_update)
    go expr@(HsVar x (L l var))
      | Just update <- lookupDNameEnv updates $ varName var = setSrcSpanA l $ do
        outputTcM "Updating type of occurrence: " expr
        return ((HsVar x (L l (new_id update))), Just (update, emptySubst))
    go expr@(HsApp x (L l f) arg) = setSrcSpanA l $ do
      outputTcM "HsApp {" expr
      (new_f, maybe_update) <- go f
      printLnTcM "}"
      return (HsApp x (L l new_f) arg, maybe_update)
    go expr = do
      outputTcM "Reached non-wrapper expr " expr
      expr' <- rewriteCallsIn updates expr
      unless (hsExprType expr `eqType` hsExprType expr') $
        failTcM $ text "Inner type is not a changed id, but its type changed " <+> ppr expr'
      return (expr', Nothing)

    mk_ev_apps subst update = do
      let vars = tyCoVarsOfTypes (new_theta update)
      let unassigned_vars = filterVarSet (`notElemSubst` subst) vars
      unless (isEmptyVarSet unassigned_vars) $ failTcM $ text "the following vars from the called function's type have not been applied at this insertion point:" <+> ppr unassigned_vars 
      let theta = substTheta subst (new_theta update)
      outputTcM "Emitting new constraints due to call with update " update
      outputTcM "New theta: " theta
      instCallConstraints (OccurrenceOf $ varName $ new_id update) theta

    maybe_mk_new :: Subst -> Maybe (UpdateInfo, Subst) -> TcM (HsWrapper, Maybe (UpdateInfo,Subst))
    maybe_mk_new _ Nothing = return (WpHole, Nothing)
    maybe_mk_new new_subst (Just (update, old_subst))
      | elemSubst (last_ty_var update) subst = do
        new_ev_apps <- mk_ev_apps subst update
        return (new_ev_apps, Nothing)
      | otherwise = return (WpHole, Just (update, subst))
      where
        subst = unionSubst new_subst old_subst

