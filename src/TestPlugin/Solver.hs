module TestPlugin.Solver (totalTcPlugin) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin

import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad (TcPlugin (..), TcPluginSolveResult (..), mapMaybeM)
import GHC.Tc.Types.Constraint (Ct, ctPred, mkNonCanonical, ctLoc, mkSimpleWC, ctEvidence, isSolvedWC)
import GHC.Core.Class (Class(..))
import GHC.Core.Predicate (getClassPredTys_maybe)
import TestPlugin.Placeholder (mkPlaceholder)
import GHC.Tc.Solver (solveWanteds)
import GHC.Tc.Solver.Monad (runTcS)

totalTcPlugin :: [CommandLineOption] -> Maybe TcPlugin
totalTcPlugin _ = Just $ 
  TcPlugin { tcPluginInit = return ()
           , tcPluginSolve = solve
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop = \_ -> return ()
           }

totalClassName :: TcPluginM Name
totalClassName = do
  Found _ md <- findImportedModule (mkModuleName "TestPlugin") NoPkgQual
  lookupOrig md (mkTcOcc "TotalClass")

wantedCtToTotal :: Ct -> TcPluginM (Maybe (EvTerm, Ct))
wantedCtToTotal ct = do
  targetTyConTy <- case getClassPredTys_maybe $ ctPred ct of
    Just (cls, _) -> return $ mkTyConTy $ classTyCon cls
    Nothing -> fail "Not a class constraint"
  totalClass <- totalClassName >>= tcLookupClass
  let predType = mkTyConApp (classTyCon totalClass) [typeKind targetTyConTy, targetTyConTy] 
  newCt <- mkNonCanonical <$> newWanted (ctLoc ct) predType
  (wc, _) <- unsafeTcPluginTcM $ runTcS $ solveWanteds (mkSimpleWC [ctEvidence newCt])
  if isSolvedWC wc then return $ Just (mkPlaceholder predType, ct) else return Nothing

solve :: () -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solve () _ _ [] = do
  return $ TcPluginSolveResult [] [] []
solve () _ _ wanteds = do
  solvedCts <- mapMaybeM wantedCtToTotal wanteds
  return $ TcPluginSolveResult 
    { tcPluginSolvedCts = solvedCts
    , tcPluginNewCts = []
    , tcPluginInsolubleCts = []
    }

output :: Outputable a => String -> a -> TcPluginM ()
output str x = tcPluginIO . putStrLn $ str ++ " " ++ showPprUnsafe x
