module TotalClassPlugin.Rewriter ( module TotalClassPlugin.Rewriter.Solve, totalTcResultAction ) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcGblEnv(..), TcM)

import TotalClassPlugin.Rewriter.Bind (rewriteBinds)
import TotalClassPlugin.Rewriter.Call (rewriteCalls)
import TotalClassPlugin.Rewriter.Solve

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ gbl = do
  (gbl', _) <- rewriteBinds' (tcg_binds gbl)
  return gbl'
  where
    rewriteBinds' binds = rewriteBinds binds rewriteCalls' 
    rewriteCalls' env binds = rewriteCalls env binds rewriteBinds'
