{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module TotalClassPlugin.Rewriter.Capture (captureAndUpdateBind, captureConstraints, wrapperLams, addToWpLet) where

import GHC.Plugins hiding (TcPlugin)
import GHC (HsBindLR(..), GhcTc, HsBind, AbsBinds (abs_tvs, abs_ev_vars, abs_ev_binds, abs_binds, AbsBinds, abs_exports, abs_sig))
import GHC.Tc.Types (TcM)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), TcEvBinds (TcEvBinds, EvBinds), EvBindsVar (ebv_binds, EvBindsVar, CoEvBindsVar), mkWpLet, extendEvBinds, emptyTcEvBinds)
import Data.Generics (GenericM, Data (gmapM))
import GHC.Tc.Utils.Monad (updTcRef)
import GHC.Tc.Types.Origin (SkolemInfoAnon (UnkSkol))

import TotalClassPlugin.Rewriter.Utils
import GHC.Tc.Utils.Unify (checkConstraints)
import GHC.Tc.Utils.Env (tcExtendNameTyVarEnv)
import GHC.Tc.Utils.TcType (mkTyVarNamePairs)
import GHC.Data.Bag (unionBags)
import GHC.Stack (emptyCallStack)

captureAndUpdateBind :: GenericM TcM -> HsBind GhcTc -> TcM (HsBind GhcTc)
captureAndUpdateBind inside b = do
  (maybe_ev_binds, b') <- reskolemiseBind b $ gmapM inside b
  case maybe_ev_binds of
    Nothing -> return b'
    Just ev_binds -> insertTcEvBinds ev_binds b'

captureConstraints :: [TyVar] -> [EvVar] -> TcM result -> TcM (TcEvBinds, result)
captureConstraints [] [] thing_inside = do
  res <- thing_inside
  return (emptyTcEvBinds, res)
captureConstraints  tvs given thing_inside = do
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

reskolemiseBind :: HsBind GhcTc -> TcM result -> TcM (Maybe TcEvBinds, result)
reskolemiseBind (FunBind {fun_ext=(wrap, _)}) thing_inside = do
  let (tvs, evs) = wrapperLams wrap
  (binds, result) <- captureConstraints tvs evs $ thing_inside
  return (Just binds, result)
reskolemiseBind (XHsBindsLR (AbsBinds { abs_tvs=tvs, abs_ev_vars=evs })) thing_inside = do
  (binds, result) <- captureConstraints tvs evs $ thing_inside
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
