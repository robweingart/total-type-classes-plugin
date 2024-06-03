module TestPlugin.Rewriter.Call (rewriteCalls) where

import GHC.Plugins hiding (TcPlugin)
import GHC (HsBindLR(..), GhcTc, HsExpr(..), XXExprGhcTc(..), HsWrap (HsWrap))
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind, TcEvBinds (TcEvBinds, EvBinds), evBindMapBinds)
import Data.Generics (everywhereM, mkM)
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


rewriteCalls :: UpdateEnv -> TcGblEnv -> (TcGblEnv -> TcM TcGblEnv) -> TcM TcGblEnv
rewriteCalls ids gbl cont
  | isEmptyDNameEnv ids = return gbl
  | otherwise = do
    binds' <- everywhereM (mkM (rewriteCallsInBind ids)) (tcg_binds gbl)
    setGblEnv gbl{tcg_binds = binds'} $ do
      gbl' <- getGblEnv
      cont gbl'


rewriteCallsInBind :: UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteCallsInBind ids b@(FunBind {}) = do
  outputTcM "Rewriting calls in bind: " b
  (b', wanteds) <- captureConstraints $ everywhereM (mkM (rewriteCall ids)) b
  if isEmptyWC wanteds then return b' else rewriteEvAfterCalls wanteds b'
rewriteCallsInBind _ b = return b

rewriteEvAfterCalls :: WantedConstraints -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteEvAfterCalls wanteds b@(FunBind {fun_ext=(wrapper, ctick)}) = do
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
  return b{fun_ext=(wrapper'', ctick)}
rewriteEvAfterCalls _ _ = fail "invalid arg"

rewriteCall :: UpdateEnv -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteCall ids expr@(XExpr (WrapExpr (HsWrap w e@(HsVar x (L l var)))))
  | Just UInfo{new_id=newId, new_theta=predTys} <- lookupDNameEnv ids (varName var) = do
    outputTcM "Found wrapped call: " expr
    outputTcM "wrapper: " ()
    printWrapper 1 w
    outputTcM "type: " $ hsExprType expr
    case hsExprType expr of
      FunTy _ _ (TyConApp _ [_, TyVarTy tyVar]) _ -> outputTcM "Ty var in arg: " $ varUnique tyVar
      _ -> return ()
    outputTcM "inner type: " $ varType var
    printBndrTys $ varType var
    
    w' <- instCallConstraints (OccurrenceOf (varName var)) predTys
    let newWrap = w' <.> w
    outputTcM "New wrapper: " () 
    printWrapper 1 newWrap
    let newExpr = XExpr (WrapExpr (HsWrap newWrap (HsVar x (L l newId))))
    outputTcM "New call: " newExpr 
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
