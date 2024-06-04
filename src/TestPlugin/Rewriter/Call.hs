{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}

module TestPlugin.Rewriter.Call (rewriteCalls) where

import GHC.Plugins hiding (TcPlugin)
import GHC (HsBindLR(..), GhcTc, HsExpr(..), XXExprGhcTc(..), HsWrap (HsWrap), GhcRn)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind, TcEvBinds (TcEvBinds, EvBinds), evBindMapBinds)
import Data.Generics (everywhereM, mkM, everywhereBut, mkQ, GenericM, GenericQ, orElse, listify, Data (gmapM), GenericQ' (unGQ, GQ))
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
import Control.Monad (unless, forM_)
import GHC.Core.TyCo.Subst (elemSubst)
import GHC.Tc.Gen.Head (HsExprArg)
import Control.Monad.State (modify, State, runState)


rewriteCalls :: UpdateEnv -> TcGblEnv -> (TcGblEnv -> TcM TcGblEnv) -> TcM TcGblEnv
rewriteCalls ids gbl cont
  | isEmptyDNameEnv ids = do
    printLnTcM "No new modified ids, ending loop"
    return gbl
  | otherwise = do
    forM_ ids $ \UInfo{new_id=id', last_ty_var=tv} -> do
      outputTcM "Id: " id'
      outputTcM "Last ty var: " $ varUnique tv
    binds' <- everywhereM (mkM (rewriteCallsInBind ids)) (tcg_binds gbl)
    setGblEnv gbl{tcg_binds = binds'} $ do
      gbl' <- getGblEnv
      cont gbl'

recordXExpr :: HsExpr GhcTc -> State [HsExpr GhcTc] (HsExpr GhcTc)
recordXExpr (XExpr (WrapExpr (HsWrap _ inner_expr))) = modify (inner_expr : ) >> return inner_expr
recordXExpr expr = return expr

rewriteCallsInBind :: UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteCallsInBind ids b@(FunBind {fun_matches=matches}) = do
  printLnTcM "rewriteCallsInBind {"
  outputTcM "Rewriting calls in bind: " b
  outputTcM "Wraps: " $ snd $ runState (everywhereM (mkM recordXExpr) matches) []
  (matches', wanteds) <- captureConstraints (rewriteWrapsAndIds ids emptyNameSet matches)
  let b' = b{fun_matches=matches'}
  res <- if isEmptyWC wanteds then return b' else rewriteEvAfterCalls wanteds b'
  printLnTcM "}"
  return res
rewriteCallsInBind _ b = return b

mkQAny ::  [GenericQ' (TcM Bool)] -> GenericQ (TcM Bool)
mkQAny qs x = foldr (\a b -> liftA2 (||) (unGQ a x) b) (return False) qs

rewriteWrapsAndIds :: UpdateEnv -> NameSet -> GenericM TcM
rewriteWrapsAndIds ids old_names y = do
  printLnTcM "rewriteWrapsAndIds {"
  r <- go y
  printLnTcM "}"
  return r
  where
    qSkip :: GenericQ (TcM Bool)
    qSkip = mkQAny [GQ $ mkQ (return False) skipNestedBind, GQ $ mkQ (return False) skipHsExprGhcRn]
    qName :: GenericQ (TcM (Maybe (NameSet, HsWrapper)))
    qName = mkQ (return Nothing) (rewriteWrapper ids old_names)
    f :: GenericM TcM
    f = mkM (rewriteVar ids old_names)
    g :: (NameSet, HsWrapper) -> GenericM TcM
    g = (\(names, w) -> mkM (rewriteXExpr ids names w))

    go :: GenericM TcM
    go x = do
      skip <- qSkip x
      if skip then return x else do
        res <- qName x
        case res of
          Nothing -> do
            x' <- f x
            gmapM go x'
          Just r -> g r x

rewriteWrapper :: UpdateEnv -> NameSet -> HsExpr GhcTc -> TcM (Maybe (NameSet, HsWrapper))
rewriteWrapper ids names expr@(XExpr (WrapExpr (HsWrap w inner_expr))) = do
  let all_us = eltsDNameEnv ids
  let subst = snd $ hsWrapperTypeSubst w (hsExprType inner_expr)
  let us = filter ((`elemSubst` subst) . last_ty_var) all_us
  case us of
    [] -> do
      --printLnTcM "No relevant names, skipping"
      return Nothing
    [UInfo{new_id=id', new_theta=theta, last_ty_var=tv}] -> do
      outputTcM "rewriteWrapper " expr 
      let name = idName id'
      outputTcM "Name we expect to find here: " name
      let theta' = substTheta subst theta
      let last_ty_arg = substTyVar subst tv
      outputTcM "Last ty var bound to: " last_ty_arg
      new_ev_apps <- instCallConstraints (OccurrenceOf name) theta'
      w' <- everywhereM (mkM (insertWrapperBefore new_ev_apps last_ty_arg)) w
      outputTcM "New wrapper: " () 
      printWrapper 1 w'
      return $ Just (extendNameSet names name, w')
    _ -> do
      outputTcM "Encountered tvs relating to multiple names: " names
      fail "Multiple names"
rewriteWrapper _ _ _ = do 
  return Nothing

insertWrapperBefore :: HsWrapper -> Type -> HsWrapper -> TcM HsWrapper
insertWrapperBefore new_w ty w@(WpTyApp ty')
  | eqType ty ty' = return $ new_w <.> w
insertWrapperBefore _ _ w = return w

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

rewriteXExpr :: UpdateEnv -> NameSet -> HsWrapper -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteXExpr ids names new_w expr@(XExpr (WrapExpr (HsWrap _ inner_expr))) = do
  outputTcM "rewriteXExpr " expr
  outputFullTcM "inner expr: " inner_expr
  outputTcM "old type of inner expr: " $ hsExprType inner_expr
  inner_expr' <- rewriteWrapsAndIds ids names inner_expr
  outputTcM "new type of inner expr: " $ hsExprType inner_expr'
  return $ XExpr (WrapExpr (HsWrap new_w inner_expr'))
rewriteXExpr _ _ _ expr = return expr

rewriteVar ::  UpdateEnv -> NameSet -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteVar ids expected_names expr@(HsVar x (L l var)) = do
  let res = lookupDNameEnv ids $ varName var
  let expected = elemNameSet (varName var) expected_names
  case (res, expected) of
    (Nothing, _) -> return expr
    (Just _, False) -> do
      outputTcM "Found occurrence of id outside last ty var application: " var
      fail "Call without wrapper"
    (Just UInfo{new_id=id'}, True) -> do 
      outputTcM "Updating type of occurrence: " expr
      return (HsVar x (L l id'))
      
rewriteVar _ _ expr = return expr

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
rewriteCall _ expr@(XExpr (WrapExpr (HsWrap w e))) = do
  outputTcM "Found WrapExpr: " expr
  let subst = snd $ hsWrapperTypeSubst w $ hsExprType e
  outputTcM "  Subst: " subst
  let (Subst _ _ tvSubstEnv _) = subst
  nonDetFoldUFM  (\case { TyVarTy var -> (>>) $ outputTcM "  ty var in subst env: " $ varUnique var; _ -> id }) (return ()) tvSubstEnv
  return expr

rewriteCall _ expr = return expr

addBindsToWpLet :: TcRef Int -> Bag EvBind -> HsWrapper -> TcM HsWrapper
addBindsToWpLet _ _ (WpLet (TcEvBinds _)) = fail "Encountered unzonked TcEvBinds, this should not happen"
addBindsToWpLet counter binds (WpLet (EvBinds binds')) = do
  let newBinds = unionBags binds binds'
  updTcRef counter (+1)
  return (WpLet (EvBinds newBinds))
addBindsToWpLet _ _ w = return w
