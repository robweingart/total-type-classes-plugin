{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}

module TestPlugin.Rewriter.Call (rewriteCalls) where

import GHC.Plugins hiding (TcPlugin)
import GHC (HsBindLR(..), GhcTc, HsExpr(..), XXExprGhcTc(..), HsWrap (HsWrap), GhcRn, LHsBind, LHsExpr, HsBind)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind, TcEvBinds (TcEvBinds, EvBinds), evBindMapBinds, isIdHsWrapper)
import Data.Generics (everywhereM, mkM, everywhereBut, mkQ, GenericM, GenericQ, orElse, listify, Data (gmapM), GenericQ' (unGQ, GQ))
import GHC.Data.Bag (unionBags, Bag)
import GHC.Core.TyCo.Rep (Type(..), Scaled (Scaled))
import GHC.Hs.Syn.Type (hsExprType)
import GHC.Tc.Utils.Monad (captureConstraints, newTcRef, setGblEnv, getGblEnv, readTcRef, updTcRef, wrapLocMA)
import GHC.Tc.Utils.Instantiate (instCallConstraints)
import GHC.Tc.Types.Origin (CtOrigin(OccurrenceOf))
import GHC.Tc.Solver (solveWanteds)
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Types.Constraint (isSolvedWC, WantedConstraints, isEmptyWC)

import TestPlugin.Rewriter.Env
import TestPlugin.Rewriter.Utils
import GHC.Core.TyCo.Compare (eqType)
import Control.Monad (unless, forM_)
import GHC.Core.TyCo.Subst (elemSubst)
import Control.Monad.State (modify, State, runState)

rewriteCalls :: UpdateEnv -> TcGblEnv -> (TcGblEnv -> TcM TcGblEnv) -> TcM TcGblEnv
rewriteCalls ids gbl cont
  | isEmptyDNameEnv ids = do
    printLnTcM "No new modified ids, ending loop"
    return gbl
  | otherwise = do
    forM_ ids (outputTcM "")
    binds' <- everywhereM (mkM (rewriteCallsInLHsBind ids)) (tcg_binds gbl)
    setGblEnv gbl{tcg_binds = binds'} $ do
      gbl' <- getGblEnv
      cont gbl'

recordXExpr :: HsExpr GhcTc -> State [HsExpr GhcTc] (HsExpr GhcTc)
recordXExpr (XExpr (WrapExpr (HsWrap _ inner_expr))) = modify (inner_expr : ) >> return inner_expr
recordXExpr expr = return expr

rewriteCallsInLHsBind :: UpdateEnv -> LHsBind GhcTc -> TcM (LHsBind GhcTc)
rewriteCallsInLHsBind updates = wrapLocMA (rewriteCallsInFunBind updates)

rewriteCallsInFunBind :: UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteCallsInFunBind ids b@(FunBind {fun_matches=matches}) = do
  printLnTcM "rewriteCallsInBind {"
  outputTcM "Rewriting calls in bind: " b
  outputTcM "Wraps: " $ snd $ runState (everywhereM (mkM recordXExpr) matches) []
  (matches', wanteds) <- captureConstraints (rewriteWrapsAndIds ids matches)
  let b' = b{fun_matches=matches'}
  res <- if isEmptyWC wanteds then return b' else rewriteEvAfterCalls wanteds b'
  printLnTcM "}"
  return res
rewriteCallsInFunBind _ b = return b

mkQAny ::  [GenericQ' (TcM Bool)] -> GenericQ (TcM Bool)
mkQAny qs x = foldr (\a b -> liftA2 (||) (unGQ a x) b) (return False) qs

rewriteWrapsAndIds :: UpdateEnv -> GenericM TcM
rewriteWrapsAndIds ids y = do
  printLnTcM "rewriteWrapsAndIds {"
  r <- go y
  printLnTcM "}"
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
skipHsExprGhcRn expr = do
  outputTcM "Skipping rn expr " expr 
  return True

noRewriteLVar :: UpdateEnv -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
noRewriteLVar updates = wrapLocMA (noRewriteVar updates)

noRewriteVar :: UpdateEnv -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
noRewriteVar updates expr@(HsVar _ (L _ var))
  | Just _ <- lookupDNameEnv updates (varName var) = failTcM (text "call to modified function " <+> ppr expr <+> text " is not immediate child of a wrapper")
noRewriteVar _ expr = return expr

rewriteLWrapExpr :: UpdateEnv -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
rewriteLWrapExpr updates = wrapLocMA (rewriteWrapExpr updates)

rewriteWrapExpr :: UpdateEnv -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteWrapExpr updates outer@(XExpr (WrapExpr (HsWrap _ _))) = do
  let old_ty = hsExprType outer
  (expr', maybe_update) <- go outer
  let new_ty = hsExprType expr'
  case (eqType old_ty new_ty, maybe_update) of
    (False, Nothing) -> failTcM (text "no update but inner type changed " <+> ppr new_ty) 
    (_, Just _) -> failTcM (text "update not resolved")
    (True, Nothing) -> return expr'
  where
    go :: HsExpr GhcTc -> TcM (HsExpr GhcTc, Maybe UpdateInfo)
    go expr@(XExpr (WrapExpr (HsWrap wrap old_inner))) = go old_inner >>= \case
      (new_inner, Just update) -> if
        | (_, subst) <- hsWrapperTypeSubst wrap (hsExprType old_inner), elemSubst (last_ty_var update) subst -> do
          let theta = substTheta subst (new_theta update)
          new_ev_apps <- instCallConstraints (OccurrenceOf $ varName $ new_id update) theta
          let new_wrap = new_ev_apps <.> wrap 
          let new_expr = XExpr (WrapExpr (HsWrap new_wrap new_inner))
          unless (hsExprType expr `eqType` hsExprType new_expr) $
            failTcM $ text "Type still different after update"
          return (new_expr, Nothing)
        | otherwise -> return (XExpr (WrapExpr (HsWrap wrap new_inner)), Just update)
      (new_inner, Nothing) -> return (XExpr (WrapExpr (HsWrap wrap new_inner)), Nothing)
    go expr@(HsVar x (L l var))
      | Just update <- lookupDNameEnv updates $ varName var = do
        outputTcM "Updating type of occurrence: " expr
        return ((HsVar x (L l (new_id update))), Just update)
    go expr = do
      expr' <- rewriteWrapsAndIds updates expr
      unless (hsExprType expr `eqType` hsExprType expr') $
        failTcM $ text "Inner type is not a changed id, but its type changed " <+> ppr expr'
      return (expr', Nothing)
rewriteWrapExpr _ expr = failTcM $ text "rewriteWrapExpr called on wrong expr type " <+> ppr expr

rewriteEvAfterCalls :: WantedConstraints -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteEvAfterCalls wanteds b@(FunBind {fun_ext=(wrapper, ctick)}) = do
  printLnTcM "rewriteEvAfterCalls {"
  outputTcM "Captured constraints: " wanteds
  (wc, ebm) <- runTcS $ solveWanteds wanteds
  outputTcM "Resulting wc: " wc
  outputTcM "Resulting ebm: " ebm
  outputTcM "solved: " $ isSolvedWC wc
  let newEvBinds = evBindMapBinds ebm
  counter <- newTcRef 0
  wrapper' <- everywhereM (mkM (addBindsToWpLet counter newEvBinds)) wrapper
  changes <- readTcRef counter
  wrapper'' <- case changes of
    0 -> return $ wrapper' <.> WpLet (EvBinds newEvBinds)
    1 -> return wrapper'
    _ -> failTcM $ text "too many WpLet"
  printLnTcM "}"
  return b{fun_ext=(wrapper'', ctick)}
rewriteEvAfterCalls _ _ = failTcM $ text "invalid arg"

addBindsToWpLet :: TcRef Int -> Bag EvBind -> HsWrapper -> TcM HsWrapper
addBindsToWpLet _ _ (WpLet (TcEvBinds _)) = failTcM $ text "Encountered unzonked TcEvBinds, this should not happen"
addBindsToWpLet counter binds (WpLet (EvBinds binds')) = do
  let newBinds = unionBags binds binds'
  updTcRef counter (+1)
  return (WpLet (EvBinds newBinds))
addBindsToWpLet _ _ w = return w
