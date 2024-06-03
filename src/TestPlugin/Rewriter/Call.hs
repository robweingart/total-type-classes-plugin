{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter.Call (rewriteCalls) where

import GHC.Plugins hiding (TcPlugin)
import GHC (HsBindLR(..), GhcTc, HsExpr(..), XXExprGhcTc(..), HsWrap (HsWrap))
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind, TcEvBinds (TcEvBinds, EvBinds), evBindMapBinds)
import Data.Generics (everywhereM, mkM, everywhereBut, mkQ)
import GHC.Data.Bag (unionBags, Bag)
import GHC.Core.TyCo.Rep (Type(..))
import GHC.Hs.Syn.Type (hsExprType)
import GHC.Tc.Utils.Monad (captureConstraints, newTcRef, setGblEnv, getGblEnv, readTcRef, updTcRef)
import GHC.Tc.Utils.Instantiate (instCallConstraints)
import GHC.Tc.Types.Origin (CtOrigin(OccurrenceOf))
import GHC.Tc.Solver (solveWanteds)
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Types.Constraint (isSolvedWC, WantedConstraints, isEmptyWC)

import TestPlugin.Rewriter.Env
import TestPlugin.Rewriter.Utils
import GHC.Core.TyCo.Compare (eqType)
import Control.Monad (unless)


rewriteCalls :: UpdateEnv -> TcGblEnv -> (TcGblEnv -> TcM TcGblEnv) -> TcM TcGblEnv
rewriteCalls ids gbl cont
  | isEmptyDNameEnv ids = return gbl
  | otherwise = do
    binds' <- everywhereM (mkM (rewriteCallsInBind ids)) (tcg_binds gbl)
    setGblEnv gbl{tcg_binds = binds'} $ do
      gbl' <- getGblEnv
      cont gbl'

rewriteCallsInBind :: UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteCallsInBind ids b@(FunBind {fun_matches=matches}) = do
  printLnTcM "rewriteCallsInBind {"
  outputTcM "Rewriting calls in bind: " b
  (matches', wanteds) <- captureConstraints $ everywhereButM (mkQ (return False) skipNestedBind) (mkM (rewriteCall ids)) matches
  let b' = b{fun_matches=matches'}
  res <- if isEmptyWC wanteds then return b' else rewriteEvAfterCalls wanteds b'
  printLnTcM "}"
  return res
rewriteCallsInBind _ b = return b

skipNestedBind :: HsBindLR GhcTc GhcTc -> TcM Bool
skipNestedBind (FunBind {fun_id=fid}) = do
  outputTcM "Skipping nested bind: " fid 
  return True
skipNestedBind _ = return False

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
    _ -> fail "too many WpLet"
  printLnTcM "}"
  return b{fun_ext=(wrapper'', ctick)}
rewriteEvAfterCalls _ _ = fail "invalid arg"

rewriteCall :: UpdateEnv -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteCall ids expr@(XExpr (WrapExpr (HsWrap w inner_expr@(HsVar x (L l var)))))
  | Just UInfo{new_id=newId, new_theta=predTys} <- lookupDNameEnv ids (varName var) = do
    printLnTcM "rewriteCall {"
    outputTcM "Found wrapped call: " expr
    outputTcM "wrapper: " ()
    printWrapper 1 w
    outputTcM "type: " $ hsExprType expr
    case hsExprType expr of
      FunTy _ _ (TyConApp _ [_, TyVarTy tyVar]) _ -> outputTcM "Ty var in arg: " $ varUnique tyVar
      _ -> return ()
    outputTcM "inner type: " $ varType var
    printBndrTys $ varType var

    let inner_ty = hsExprType inner_expr
    let outer_ty = hsExprType expr
    let (wrapped_ty, subst) = hsWrapperTypeSubst w inner_ty
    outputTcM "Computed outer type: " wrapped_ty
    unless (eqType outer_ty wrapped_ty) $ fail "hsWrapperTypeSubst type mismatch"
    outputTcM "Subst: " subst
    let (Subst _ _ tvSubstEnv _) = subst
    nonDetFoldUFM  (\case { TyVarTy var -> (>>) $ outputTcM "ty var in subst env: " $ varUnique var; _ -> id }) (return ()) tvSubstEnv
    let theta = substTheta subst predTys
    outputTcM "Constraints to add: " $ theta
    w' <- instCallConstraints (OccurrenceOf (varName var)) theta
    let newWrap = w' <.> w
    outputTcM "New wrapper: " () 
    printWrapper 1 newWrap
    let (new_wrapped_ty, _) = hsWrapperTypeSubst w inner_ty
    outputTcM "New computed outer type: " new_wrapped_ty
    unless (eqType outer_ty new_wrapped_ty) $ fail "adding theta changed type"
    let newExpr = XExpr (WrapExpr (HsWrap newWrap (HsVar x (L l newId))))
    let (wrapped2, subst2) = hsWrapperTypeSubst newWrap $ varType newId
    outputTcM "New computed outer type 2: " $ wrapped2
    outputTcM "New subst: " $ subst2
    outputTcM "New call: " newExpr 
    printLnTcM "rewriteCall }"
    return newExpr
  | otherwise = return expr
rewriteCall _ expr = return expr

addBindsToWpLet :: TcRef Int -> Bag EvBind -> HsWrapper -> TcM HsWrapper
addBindsToWpLet _ _ (WpLet (TcEvBinds _)) = fail "Encountered unzonked TcEvBinds, this should not happen"
addBindsToWpLet counter binds (WpLet (EvBinds binds')) = do
  let newBinds = unionBags binds binds'
  updTcRef counter (+1)
  return (WpLet (EvBinds newBinds))
addBindsToWpLet _ _ w = return w
