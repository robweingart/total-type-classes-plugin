{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}

module TestPlugin.Rewriter.Call (rewriteCalls) where

import GHC.Plugins hiding (TcPlugin)
import GHC (HsBindLR(..), GhcTc, HsExpr(..), XXExprGhcTc(..), HsWrap (HsWrap), GhcRn)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind, TcEvBinds (TcEvBinds, EvBinds), evBindMapBinds, isIdHsWrapper)
import Data.Generics (everywhereM, mkM, everywhereBut, mkQ, GenericM, GenericQ, orElse, listify, Data (gmapM), GenericQ' (unGQ, GQ))
import GHC.Data.Bag (unionBags, Bag)
import GHC.Core.TyCo.Rep (Type(..), Scaled (Scaled))
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
import Control.Monad.State (modify, State, runState)
import qualified Data.Map as M


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
  names_ref <- newTcRef emptyNameSet
  (matches', wanteds) <- captureConstraints (rewriteWrapsAndIds ids names_ref matches)
  let b' = b{fun_matches=matches'}
  res <- if isEmptyWC wanteds then return b' else rewriteEvAfterCalls wanteds b'
  printLnTcM "}"
  return res
rewriteCallsInBind _ b = return b

mkQAny ::  [GenericQ' (TcM Bool)] -> GenericQ (TcM Bool)
mkQAny qs x = foldr (\a b -> liftA2 (||) (unGQ a x) b) (return False) qs

rewriteWrapsAndIds :: UpdateEnv -> TcRef NameSet -> GenericM TcM
rewriteWrapsAndIds ids namesRef y = do
  printLnTcM "rewriteWrapsAndIds {"
  r <- go y
  printLnTcM "}"
  return r
  where
    qSkip :: GenericQ (TcM Bool)
    qSkip = mkQAny [GQ $ mkQ (return False) skipNestedBind, GQ $ mkQ (return False) skipHsExprGhcRn]
    qWrap :: GenericQ (TcM Bool)
    qWrap = mkQ (return False) isWrapper
    f :: GenericM TcM
    f = mkM (rewriteVar ids namesRef)
    g :: GenericM TcM
    g = mkM (rewriteXExpr ids namesRef)

    go :: GenericM TcM
    go x = do
      skip <- qSkip x
      if skip then return x else do
        isWrap <- qWrap x
        if isWrap then do g x
        else do
          x' <- f x
          gmapM go x'

isWrapper ::  HsExpr GhcTc -> TcM Bool
isWrapper (XExpr (WrapExpr (HsWrap w inner_expr))) = return True
isWrapper _ = return False

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
    _ -> failTcM "too many WpLet"
  printLnTcM "}"
  return b{fun_ext=(wrapper'', ctick)}
rewriteEvAfterCalls _ _ = failTcM "invalid arg"

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
      failTcM "Multiple names"
rewriteWrapper _ _ _ = do 
  return Nothing

rewriteXExpr :: UpdateEnv -> TcRef NameSet -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteXExpr ids names_ref expr@(XExpr (WrapExpr (HsWrap w inner_expr))) = do
  outputTcM "rewriteXExpr " expr
  outputFullTcM "inner expr: " inner_expr
  new_names_ref <- newTcRef emptyNameSet
  inner_expr' <- rewriteWrapsAndIds ids new_names_ref inner_expr
  let outer_ty = hsExprType expr
  let inner_ty = hsExprType inner_expr
  let inner_ty' = hsExprType inner_expr'
  if eqType inner_ty inner_ty' then return expr else do
    outputTcM "old type of outer expr: " $ outer_ty
    outputTcM "old type of inner expr: " $ inner_ty
    printBndrTys inner_ty
    outputTcM "new type of inner expr: " $ inner_ty'
    printBndrTys inner_ty'
    let subst = snd $ hsWrapperTypeSubst w (hsExprType inner_expr)
    outputTcM "Subst: " subst
    let (outer_bndrs, _) = splitInvisPiTys (hsExprType expr)
    let (inner_bndrs, _) = splitInvisPiTys (hsExprType inner_expr)
    let (new_inner_bndrs, _) = splitInvisPiTys (hsExprType inner_expr')
    let relevant_bndrs = reverse $ dropList outer_bndrs $ reverse inner_bndrs
    outputTcM "Relevant binders: " relevant_bndrs
    new_names <- readTcRef new_names_ref
    let relevant_us = filterDNameEnv ((`elemNameSet` new_names) . idName . new_id) ids
    --let us' = mkVarEnv $ map (\UInfo{new_id=id', new_theta=theta, last_ty_var=tv} -> (substTyVar subst tv, (idName id', substTheta subst theta))) us
    new_wraps <- instRelevantCallConstraints relevant_us subst relevant_bndrs new_inner_bndrs
    (new_w, remaining_bndrs) <- insertEvApps w new_wraps
    case remaining_bndrs of
      [] -> return $ XExpr (WrapExpr (HsWrap new_w inner_expr'))
      _ -> failTcM "Too many new wrappers"
rewriteXExpr _ _ expr = return expr

instRelevantCallConstraints :: UpdateEnv -> Subst -> [PiTyBinder] -> [PiTyBinder] -> TcM [HsWrapper]
instRelevantCallConstraints updates subst old_relevant_bndrs new_bndrs = go old_relevant_bndrs new_bndrs [] >>= mapM inst 
  where
    go [] _ acc = return acc
    go ((Named (Bndr tv _)) : bs) ((Named (Bndr tv' _)) : bs') tss = go bs bs' ((tv, []) : tss)
    go ((Anon (Scaled m t) f) : bs) ((Anon (Scaled m' t') f') : bs') tss
      | eqType m m' && eqType t t' && f == f' = go bs bs' tss
    go bs ((Anon (Scaled _ ty) _) : bs') ((tv, ts) : tss) = go bs bs' ((tv, ty : ts) : tss)
    go _ _ _ = failTcM "binders don't match"

    names_matching tv = map (idName . new_id) $ eltsDNameEnv $ filterDNameEnv ((== tv) . last_ty_var) updates 

    get_name tv = case names_matching tv of
      [] -> failTcM "no name matches"
      [n] -> return n
      _ -> failTcM "ambiguous"
    
    inst (_, []) = return WpHole
    inst (tv, tss) = do
      name <- get_name tv
      let theta = substTheta subst $ reverse tss
      instCallConstraints (OccurrenceOf name) theta
        
insertEvApps :: HsWrapper -> [HsWrapper] -> TcM (HsWrapper, [HsWrapper])
insertEvApps WpHole ws = return (WpHole, ws) 
insertEvApps (WpCompose w1 w2) ws = do
  (w2', ws1) <- insertEvApps w2 ws
  (w1', ws2) <- insertEvApps w1 ws1
  return (w1' <.> w2', ws2)
insertEvApps (WpFun _ _ _) _ = failTcM "WpFun unsupported"
insertEvApps (WpCast _) _ = failTcM "WpCast unsupported"
insertEvApps (WpEvLam _) _ = failTcM "unexpected ev lambda"
insertEvApps w@(WpEvApp _) ws = return (w, ws)
insertEvApps (WpTyLam _) _ = failTcM "unexpected ty lambda"
insertEvApps w@(WpTyApp _) (new_w : ws) = return (new_w <.> w, ws)
insertEvApps (WpTyApp _) [] = failTcM "not enough new wrappers"
insertEvApps (WpLet _) _ = failTcM "unexpected WpLet"
insertEvApps (WpMultCoercion _) _ = failTcM "WpMultCoercion unsupported"

rewriteVar ::  UpdateEnv -> TcRef NameSet -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteVar ids namesRef expr@(HsVar x (L l var)) = do
  let res = lookupDNameEnv ids $ varName var
  case res of
    Nothing -> return expr
    Just UInfo{new_id=id'} -> do 
      outputTcM "Updating type of occurrence: " expr
      updTcRef namesRef (`extendNameSet` varName var)
      return (HsVar x (L l id'))
rewriteVar _ _ expr = return expr

addBindsToWpLet :: TcRef Int -> Bag EvBind -> HsWrapper -> TcM HsWrapper
addBindsToWpLet _ _ (WpLet (TcEvBinds _)) = failTcM "Encountered unzonked TcEvBinds, this should not happen"
addBindsToWpLet counter binds (WpLet (EvBinds binds')) = do
  let newBinds = unionBags binds binds'
  updTcRef counter (+1)
  return (WpLet (EvBinds newBinds))
addBindsToWpLet _ _ w = return w
