module TestPlugin.Rewriter (totalTcResultAction) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcGblEnv(..), TcM)

import GHC.Tc.Solver (captureTopConstraints, simplifyTop)
import GHC.Tc.Utils.Monad (setGblEnv, restoreEnvs, readTcRef)
import TestPlugin.Rewriter.Bind (rewriteBinds)
import TestPlugin.Rewriter.Call (rewriteCalls)
import TestPlugin.Rewriter.Utils (printLnTcM, failTcM)
import Control.Monad (unless)
import GHC.Data.Bag (isEmptyBag)
import Data.Generics (everywhereM, mkM)
import GHC.Tc.Types.Evidence (HsWrapper (WpLet), TcEvBinds (TcEvBinds, EvBinds), EvBindsVar (ebv_binds, EvBindsVar), evBindMapBinds)

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ gbl = do
  printLnTcM  "totalTcResultAction {"
  ((gbl', lcl), lie) <- setGblEnv gbl $ captureTopConstraints $ rewriteBinds' (tcg_binds gbl)
  new_ev_binds <- restoreEnvs (gbl', lcl) $ simplifyTop lie
  unless (isEmptyBag new_ev_binds) $ failTcM $ text "rewriter produced global constraints"
  binds' <- everywhereM (mkM zonkWpLet) (tcg_binds gbl')
  printLnTcM  "}"
  return gbl'{tcg_binds=binds'}
  where
    rewriteBinds' binds = rewriteBinds binds rewriteCalls' 
    rewriteCalls' env binds = rewriteCalls env binds rewriteBinds'

zonkWpLet :: HsWrapper -> TcM HsWrapper
zonkWpLet (WpLet (TcEvBinds (EvBindsVar{ebv_binds=var}))) = (WpLet . EvBinds . evBindMapBinds) <$> readTcRef var
zonkWpLet w = return w

--addToWpLet :: Bag EvBind -> HsWrapper -> TcM HsWrapper 
--addToWpLet new_binds wrap = do
--  counter <- newTcRef (0 :: Int)
--  let
--    go WpHole = return WpHole
--    go (WpCompose w1 w2) = liftA2 (<.>) (go w1) (go w2)
--    go (WpFun _ _ _) = failTcM $ text "unexpected WpFun"
--    go (WpLet (EvBinds binds)) = do
--      updTcRef counter (+1) :: TcM ()
--      return $ WpLet (EvBinds (binds `unionBags` new_binds))
--    go (WpLet (TcEvBinds _)) = failTcM $ text "Encountered unzonked TcEvBinds, this should not happen"
--    go w = return w
--  w' <- go wrap
--  readTcRef counter >>= \case
--    0 -> return $ w' <.> WpLet (EvBinds new_binds)
--    1 -> return w'
--    _ -> failTcM $ text "Too many WpLet"
