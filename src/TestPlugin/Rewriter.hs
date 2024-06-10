module TestPlugin.Rewriter ( module TestPlugin.Rewriter.Solve, totalTcResultAction ) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcGblEnv(..), TcM)

import GHC.Tc.Solver (captureTopConstraints, simplifyTop)
import GHC.Tc.Utils.Monad (setGblEnv, restoreEnvs, readTcRef)
import Control.Monad (unless)
import GHC.Data.Bag (isEmptyBag)
import Data.Generics (everywhereM, mkM)
import GHC.Tc.Types.Evidence (HsWrapper (WpLet), TcEvBinds (TcEvBinds, EvBinds), EvBindsVar (ebv_binds, EvBindsVar), evBindMapBinds)

import TestPlugin.Rewriter.Bind (rewriteBinds)
import TestPlugin.Rewriter.Call (rewriteCalls)
import TestPlugin.Rewriter.Utils (printLnTcM, failTcM)
import TestPlugin.Rewriter.Solve


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
