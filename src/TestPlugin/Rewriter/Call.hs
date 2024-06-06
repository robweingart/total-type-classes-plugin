{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}

module TestPlugin.Rewriter.Call (rewriteCalls) where

import GHC.Plugins hiding (TcPlugin)
import GHC (HsBindLR(..), GhcTc, HsExpr(..), XXExprGhcTc(..), HsWrap (HsWrap), GhcRn, LHsBind, LHsExpr, LHsBinds)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcLclEnv)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind, TcEvBinds (TcEvBinds, EvBinds), evBindMapBinds, isEmptyEvBindMap, EvBindsVar (ebv_binds, EvBindsVar, CoEvBindsVar), mkWpLet)
import Data.Generics (everywhereM, mkM, mkQ, GenericM, GenericQ, Data (gmapM), GenericQ' (unGQ, GQ))
import GHC.Hs.Syn.Type (hsExprType)
import GHC.Tc.Utils.Monad (captureConstraints, newTcRef, readTcRef, updTcRef, writeTcRef, wrapLocMA, getEnvs, updGblEnv, restoreEnvs, setGblEnv)
import GHC.Tc.Utils.Instantiate (instCallConstraints)
import GHC.Tc.Types.Origin (CtOrigin(OccurrenceOf), SkolemInfoAnon (UnkSkol))

import TestPlugin.Rewriter.Env
import TestPlugin.Rewriter.Utils
import GHC.Core.TyCo.Compare (eqType)
import Control.Monad (unless, forM_)
import GHC.Core.TyCo.Subst (elemSubst)
import GHC.Tc.Utils.Unify (checkConstraints)
import GHC.Tc.Utils.Env (tcExtendNameTyVarEnv)
import GHC.Tc.Utils.TcType (mkTyVarNamePairs)
import GHC.Data.Bag (Bag, unionBags, isEmptyBag, emptyBag)
import GHC.Tc.Solver (captureTopConstraints, simplifyTop)
import GHC.Stack (emptyCallStack)
import Data.Maybe (isJust)

rewriteCalls :: UpdateEnv -> LHsBinds GhcTc -> (LHsBinds GhcTc -> TcM (TcGblEnv, TcLclEnv)) -> TcM (TcGblEnv, TcLclEnv)
rewriteCalls ids binds cont
  | isEmptyDNameEnv ids = do
    printLnTcM "No new modified ids, ending loop"
    --outputFullTcM "Full: " binds
    getEnvs
  | otherwise = do
    forM_ ids (outputTcM "")
    (binds', lie) <- captureTopConstraints $ everywhereM (mkM (rewriteCallsInLHsBind ids)) binds
    (gbl, lcl) <- getEnvs
    new_ev_binds <- restoreEnvs (gbl, lcl) $ simplifyTop lie
    unless (isEmptyBag new_ev_binds) $ failTcM $ text "rewriter produced global constraints"
    binds'' <- mergeAllWpLets binds'
    setGblEnv gbl{tcg_binds=binds''} $ do
      cont binds''

mergeAllWpLets :: GenericM TcM
mergeAllWpLets = go
  where
    go :: GenericM TcM
    go x = if (mkQ False (const True :: HsWrapper -> Bool)) x then (mkM mergeWpLet) x else gmapM go x

-- Precondition: The wrapper is ((((w <.> WpLet) ...) <.> WpLet) <.> WpLet)
-- where w is (w1 <.> (w2 <.> (... (wn <.> WpLet))))
-- and none of the w1, ... wn contain any WpLet
-- Returns (w1 <.> (w2 <.> (... (wn <.> WpLet (EvBinds ebs)))))
-- where ebs contains the binds of all the WpLet in the input. 
mergeWpLet :: HsWrapper -> TcM HsWrapper
mergeWpLet wrap = withTcRef (Just 0 :: Maybe Int) (\ref -> everywhereM (mkM (count_let ref)) wrap) >>= \case
  (Just 0, _) -> return wrap
  (Just 1, _) -> return wrap
  _ -> do
    wrap' <- go wrap
    withTcRef (Just 0 :: Maybe Int) (\ref -> everywhereM (mkM (count_let ref)) wrap') >>= \case
      (Just 0, _) -> return wrap'
      (Just 1, _) -> do
        printLnTcM "mergeWpLet turned" 
        printWrapper 1 wrap
        printLnTcM "into"
        printWrapper 1 wrap'
        return wrap'
      (Just _, _) -> failTcM $ text "Encountered multiple WpLet after merging"
      (Nothing, _) -> failTcM $ text "Encountered EvBindsVar after merging"
  where
    go (WpCompose (WpCompose w (WpLet ev1)) (WpLet ev2)) = do
      w' <- mergeTcEvBinds ev1 ev2
      go (w <.> w') 
    go (WpCompose (WpCompose w1 w2) (WpLet ev)) = do
      wp_let' <- (mkWpLet . EvBinds) <$> rezonkTcEvBinds ev
      go (w1 <.> (w2 <.> wp_let'))
    go (WpCompose (WpLet ev1) (WpLet ev2)) = mergeTcEvBinds ev1 ev2
    go (WpCompose w1 w2) = (w1 <.>) <$> go w2
    go (WpLet ev) = (mkWpLet . EvBinds) <$> rezonkTcEvBinds ev
    go w = return w

    count_let ref w@(WpLet (TcEvBinds _)) = writeTcRef ref Nothing >> return w
    count_let ref w@(WpLet (EvBinds _)) = updTcRef ref (fmap (+1)) >> return w
    count_let _ w = return w

mergeTcEvBinds :: TcEvBinds -> TcEvBinds -> TcM HsWrapper
mergeTcEvBinds x y = (mkWpLet . EvBinds) <$> liftA2 unionBags (rezonkTcEvBinds x) (rezonkTcEvBinds y)

rezonkTcEvBinds :: TcEvBinds -> TcM (Bag EvBind)
rezonkTcEvBinds (TcEvBinds (CoEvBindsVar{})) = return emptyBag
rezonkTcEvBinds (TcEvBinds (EvBindsVar{ebv_binds=var})) = evBindMapBinds <$> readTcRef var
rezonkTcEvBinds (EvBinds ebs) = return ebs

rewriteCallsInLHsBind :: UpdateEnv -> LHsBind GhcTc -> TcM (LHsBind GhcTc)
rewriteCallsInLHsBind updates = wrapLocMA (rewriteCallsInFunBind updates)

rewriteCallsInFunBind :: UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteCallsInFunBind ids b@(FunBind {fun_matches=matches, fun_ext=(wrap, ctick)}) = do
  printLnTcM "rewriteCallsInBind {"
  outputTcM "Rewriting calls in bind: " b
  --outputTcM "Wraps: " $ snd $ runState (everywhereM (mkM recordXExpr) matches) []
  (wrap', matches') <- reskolemise wrap $ rewriteWrapsAndIds ids matches
  printLnTcM "}"
  return b{fun_matches=matches', fun_ext=(wrap', ctick)}
rewriteCallsInFunBind _ b = return b

reskolemise :: HsWrapper -> TcM result -> TcM (HsWrapper, result)
reskolemise wrap thing_inside = wrapperLams wrap >>= \case
  ([], []) -> do
    res <- thing_inside
    return (wrap, res)
  (tvs, given) -> do
    printLnTcM "reskolemise {"
    printWrapper 1 wrap
    (new_ev_binds, result) <- 
      checkConstraints (UnkSkol emptyCallStack) tvs given $
      tcExtendNameTyVarEnv (mkTyVarNamePairs tvs) thing_inside
    let new_wrap = wrap <.> mkWpLet new_ev_binds
    outputTcM "} New ev binds:" new_ev_binds
    printLnTcM "New wrapper:"
    printWrapper 1 new_wrap
    return (new_wrap, result)

wrapperLams :: HsWrapper -> TcM ([TyVar], [EvVar])
wrapperLams w = go w ([], [])
  where
    go :: HsWrapper -> ([TyVar], [EvVar]) -> TcM ([TyVar], [EvVar])
    go WpHole vs = return vs
    go (WpCompose w1 w2) vs = go w2 vs >>= go w1
    go (WpFun _ _ _) _ = failTcM $ text "unexpected WpFun"
    go (WpTyLam tv) (tvs, evs) = return (tv : tvs, evs)
    go (WpEvLam ev) (tvs, evs) = return (tvs, ev : evs)
    go _ vs = return vs

mkQAny ::  [GenericQ' (TcM Bool)] -> GenericQ (TcM Bool)
mkQAny qs x = foldr (\a b -> liftA2 (||) (unGQ a x) b) (return False) qs

rewriteWrapsAndIds :: UpdateEnv -> GenericM TcM
rewriteWrapsAndIds ids y = do
  --printLnTcM "rewriteWrapsAndIds {"
  r <- go y
  --printLnTcM "}"
  return r
  where
    qSkip :: GenericQ (TcM Bool)
    qSkip = mkQAny [GQ $ mkQ (return False) skipNestedBind, GQ $ mkQ (return False) skipHsExprGhcRn]
    qWrap :: GenericQ (TcM Bool)
    qWrap = mkQ (return False) isLWrapExpr
    f :: GenericM TcM
    f = mkM (noRewriteLVar ids)
    g :: GenericM TcM
    g = mkM (rewriteLWrapExpr ids)

    go :: GenericM TcM
    go x = do
      skip <- qSkip x
      if skip then return x else do
        isWrap <- qWrap x
        if isWrap then do g x
        else do
          x' <- f x
          gmapM go x'

isLWrapExpr :: LHsExpr GhcTc -> TcM Bool
isLWrapExpr (L _(XExpr (WrapExpr (HsWrap _ _)))) = return True
isLWrapExpr _ = return False

skipNestedBind :: HsBindLR GhcTc GhcTc -> TcM Bool
skipNestedBind (FunBind {fun_id=fid}) = do
  outputTcM "skipNestedBind" fid
  outputTcM "Skipping nested bind: " fid 
  return True
skipNestedBind _ = do
  return False

skipHsExprGhcRn :: HsExpr GhcRn -> TcM Bool
skipHsExprGhcRn _ = return True

noRewriteLVar :: UpdateEnv -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
noRewriteLVar updates = wrapLocMA (noRewriteVar updates)

noRewriteVar :: UpdateEnv -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
noRewriteVar updates expr@(HsVar _ (L _ var))
  | Just _ <- lookupDNameEnv updates (varName var) = failTcM $ text "call to modified function " <+> ppr expr <+> text " is not immediate child of a wrapper"
noRewriteVar _ expr = return expr

rewriteLWrapExpr :: UpdateEnv -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
rewriteLWrapExpr updates = wrapLocMA (rewriteWrapExpr updates)

rewriteWrapExpr :: UpdateEnv -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteWrapExpr updates outer@(XExpr (WrapExpr (HsWrap _ _))) = do
  let old_ty = hsExprType outer
  (expr', maybe_update) <- go outer
  let new_ty = hsExprType expr'
  case (eqType old_ty new_ty, maybe_update) of
    (False, Nothing) -> failTcM $ text "no update but inner type changed " <+> ppr new_ty
    (_, Just _) -> failTcM $ text "update not resolved"
    (True, Nothing) -> return expr'
  where
    go :: HsExpr GhcTc -> TcM (HsExpr GhcTc, Maybe UpdateInfo)
    go expr@(XExpr (WrapExpr (HsWrap wrap old_inner))) = do 
      (wrap', (new_ev_apps, new_inner, maybe_update)) <- reskolemise wrap $ do 
        (new_inner, maybe_update) <- go old_inner
        (new_ev_apps, maybe_update') <- maybe_mk_new wrap old_inner maybe_update
        return (new_ev_apps, new_inner, maybe_update')
      let new_wrap = new_ev_apps <.> wrap'
      let new_expr = XExpr (WrapExpr (HsWrap new_wrap new_inner))
      unless (isJust maybe_update || hsExprType expr `eqType` hsExprType new_expr) $
        failTcM $ text "Type still different after update:" <+> (vcat $
          [ text "old:" <+> ppr (hsExprType expr)
          , text "new:" <+> ppr (hsExprType new_expr)
          ])
      return (new_expr, maybe_update)
    go expr@(HsVar x (L l var))
      | Just update <- lookupDNameEnv updates $ varName var = do
        outputTcM "Updating type of occurrence: " expr
        return ((HsVar x (L l (new_id update))), Just update)
    go expr = do
      expr' <- rewriteWrapsAndIds updates expr
      unless (hsExprType expr `eqType` hsExprType expr') $
        failTcM $ text "Inner type is not a changed id, but its type changed " <+> ppr expr'
      return (expr', Nothing)

    maybe_mk_new :: HsWrapper -> HsExpr GhcTc -> Maybe UpdateInfo -> TcM (HsWrapper, Maybe UpdateInfo)
    maybe_mk_new wrap _ Nothing = do
      printLnTcM "Skipping wrapper (already done):"
      printWrapper 1 wrap
      return (WpHole, Nothing)
    maybe_mk_new wrap old_inner (Just update)
      | (_, subst) <- hsWrapperTypeSubst wrap (hsExprType old_inner), elemSubst (last_ty_var update) subst = do
        printLnTcM "Updating wrapper:"
        printWrapper 1 wrap
        let theta = substTheta subst (new_theta update)
        new_ev_apps <- instCallConstraints (OccurrenceOf $ varName $ new_id update) theta
        let new_wrap = new_ev_apps
        printLnTcM "New wrapper:"
        printWrapper 1 new_wrap
        return (new_wrap, Nothing)
      | otherwise = do 
        printLnTcM "Skipping wrapper (ty lam not found):"
        printWrapper 1 wrap
        return (WpHole, Just update)
rewriteWrapExpr _ expr = failTcM $ text "rewriteWrapExpr called on wrong expr type " <+> ppr expr
