module TestPlugin.Rewriter (totalTcResultAction) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcGblEnv(..), TcM)

import GHC.Tc.Solver (captureTopConstraints)
import GHC.Tc.Utils.Monad (setGblEnv)
import TestPlugin.Rewriter.Bind (rewriteBinds)
import TestPlugin.Rewriter.Call (rewriteCalls)
import TestPlugin.Rewriter.Utils (printLnTcM, failTcM)
import GHC.Tc.Types.Constraint (isSolvedWC)
import Control.Monad (unless)

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ gbl = do
  printLnTcM  "totalTcResultAction {"
  ((gbl', _), lie) <- setGblEnv gbl $ captureTopConstraints $ rewriteBinds' (tcg_binds gbl)
  unless (isSolvedWC lie) $ failTcM $ text "Uncaptured constraints"
  printLnTcM  "}"
  return gbl'
  where
    rewriteBinds' binds = rewriteBinds binds rewriteCalls' 
    rewriteCalls' env binds = rewriteCalls env binds rewriteBinds'
