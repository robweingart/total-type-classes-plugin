module TestPlugin.Solver (totalTcPlugin) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin

import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad (TcPlugin (..), TcPluginSolveResult (..), mapAndUnzipM)
import GHC.Tc.Types.Constraint (Ct, ctPred, mkNonCanonical, ctLoc)
import GHC.Core.Class (Class(..))
import GHC.Core.Predicate (getClassPredTys_maybe)
import TestPlugin.Placeholder (mkPlaceholder)

totalTcPlugin :: [CommandLineOption] -> Maybe TcPlugin
totalTcPlugin _ = Just $ 
  TcPlugin { tcPluginInit = return ()
           , tcPluginSolve = solve
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop = \_ -> return ()
           }

canBeTotalCt :: Ct -> Bool
canBeTotalCt ct = case getClassPredTys_maybe $ ctPred ct of
  Just (cls, _) -> all (isAlgType . varType) (classTyVars cls)
  Nothing -> False

totalClassName :: TcPluginM Name
totalClassName = do
  Found _ md <- findImportedModule (mkModuleName "TestPlugin") NoPkgQual
  lookupOrig md (mkTcOcc "TotalClass")

wantedCtToTotal :: Ct -> TcPluginM ((EvTerm, Ct), Ct)
wantedCtToTotal ct = do
  targetTyConTy <- case getClassPredTys_maybe $ ctPred ct of
    Just (cls, _) -> return $ mkTyConTy $ classTyCon cls
    Nothing -> fail "Not a class constraint"
  totalClass <- totalClassName >>= tcLookupClass
  let predType = mkTyConApp (classTyCon totalClass) [typeKind targetTyConTy, targetTyConTy] 
  newCt <- mkNonCanonical <$> newWanted (ctLoc ct) predType
  return ((mkPlaceholder predType, ct), newCt)

solve :: () -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solve () _ _ [] = do
  return $ TcPluginSolveResult [] [] []
solve () _ _ wanteds = do
  (solvedCts, newCts) <- mapAndUnzipM wantedCtToTotal $ filter canBeTotalCt wanteds
  output "Adding TotalClass constraints:" newCts
  return $ TcPluginSolveResult 
    { tcPluginSolvedCts = solvedCts
    , tcPluginNewCts = newCts
    , tcPluginInsolubleCts = []
    }

output :: Outputable a => String -> a -> TcPluginM ()
output str x = tcPluginIO . putStrLn $ str ++ " " ++ showPprUnsafe x
