module TestPlugin.Rewriter (totalTcResultAction) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcGblEnv, TcM)

import TestPlugin.Rewriter.Bind (rewriteBinds)
import TestPlugin.Rewriter.Call (rewriteCalls)

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ = rewriteBinds'
  where
    rewriteBinds' gbl' = rewriteBinds gbl' rewriteCalls' 
    rewriteCalls' env gbl' = rewriteCalls env gbl' rewriteBinds'
