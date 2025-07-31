module TotalClassPlugin.Solver (totalTcPlugin) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin
import GHC.Tc.Types.Constraint (Ct)
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad (TcPlugin (..), TcPluginSolveResult (..), mapMaybeM)
import TotalClassPlugin.Checker.Solve (solveCheck)
import TotalClassPlugin.Rewriter.Solve (solveWithPlaceholder)

totalTcPlugin :: [CommandLineOption] -> Maybe TcPlugin
totalTcPlugin _ =
  Just $
    TcPlugin
      { tcPluginInit = return (),
        tcPluginSolve = solve,
        tcPluginRewrite = const emptyUFM,
        tcPluginStop = \_ -> return ()
      }

solveCt :: [Ct] -> Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveCt givens ct = do
  res1 <- solveCheck givens ct
  case res1 of
    Just res -> return $ Just res
    Nothing -> solveWithPlaceholder givens ct

solve :: () -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solve () _ _ [] = do
  return $ TcPluginSolveResult [] [] []
solve () _ givens wanteds = do
  solvedCts <- mapMaybeM (solveCt givens) wanteds
  return $
    TcPluginSolveResult
      { tcPluginSolvedCts = solvedCts,
        tcPluginNewCts = [],
        tcPluginInsolubleCts = []
      }
