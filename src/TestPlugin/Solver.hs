module TestPlugin.Solver (totalTcPlugin) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin

import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad (TcPlugin (..), TcPluginSolveResult (..), mapMaybeM)
import GHC.Tc.Types.Constraint (Ct)

import TestPlugin.Rewriter.Solve (solveWithPlaceholder)
import TestPlugin.Checker.Solve (solveCheck)

totalTcPlugin :: [CommandLineOption] -> Maybe TcPlugin
totalTcPlugin _ = Just $ 
  TcPlugin { tcPluginInit = return ()
           , tcPluginSolve = solve
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop = \_ -> return ()
           }

solveCt :: Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveCt ct = do
  res1 <- solveCheck ct
  case res1 of
    Just res -> return $ Just res
    Nothing -> solveWithPlaceholder ct

solve :: () -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solve () _ _ [] = do
  return $ TcPluginSolveResult [] [] []
solve () _ _ wanteds = do
  solvedCts <- mapMaybeM solveCt wanteds
  return $ TcPluginSolveResult 
    { tcPluginSolvedCts = solvedCts
    , tcPluginNewCts = []
    , tcPluginInsolubleCts = []
    }
