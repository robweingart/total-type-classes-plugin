module TotalClassPlugin.Rewriter (module TotalClassPlugin.Rewriter.Solve, totalTcResultAction) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcGblEnv (..), TcM)
import TotalClassPlugin.Rewriter.Bind (rewriteBinds)
import TotalClassPlugin.Rewriter.Call (rewriteCalls)
import TotalClassPlugin.Rewriter.Solve
import TotalClassPlugin.Rewriter.Utils (failTcM)
import TotalClassPlugin.Rewriter.Env (UpdateInfo(new_id))
import Data.Foldable (Foldable(toList))

maxIterations :: Int
maxIterations = 100

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ gbl = do
  (gbl', _) <- rewriteBinds' 0 (tcg_binds gbl)
  return gbl'
  where
    rewriteBinds' n binds = rewriteBinds binds (rewriteCalls' n)
    rewriteCalls' n env binds =
      if not (isEmptyDNameEnv env) && n >= maxIterations
        then
          failTcM (text "Exceeded maximum rewriter iterations!"
                   $$ text "The following ids likely triggered an infinite rewriting loop:"
                   $$ ppr (map new_id $ toList env))
        else rewriteCalls env binds (rewriteBinds' (n + 1))
