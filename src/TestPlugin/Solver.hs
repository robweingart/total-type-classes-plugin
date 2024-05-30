module TestPlugin.Solver (totalTcPlugin) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin

import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad (TcPlugin (..), TcPluginSolveResult (..), mapAndUnzipM)
import GHC.Tc.Types.Constraint (Ct, ctPred, mkNonCanonical, ctLoc)
import Data.List (partition)
import GHC.Core.Class (Class(..))
import GHC.Core.Predicate (getClassPredTys_maybe)

totalTcPlugin :: [CommandLineOption] -> Maybe TcPlugin
totalTcPlugin _ = Just $ 
  TcPlugin { tcPluginInit = return ()
           , tcPluginSolve = solve
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop = \_ -> return ()
           }

canBeTotal :: Class -> Bool
canBeTotal cls = case classTyVars cls of
  [var] -> isAlgType (varType var) 
  _ -> False

canBeTotalCt :: Ct -> Bool
canBeTotalCt ct = case getClassPredTys_maybe $ ctPred ct of
  Just (cls, _) -> canBeTotal cls
  Nothing -> False

totalClassName :: TcPluginM Name
totalClassName = do
  Found _ md <- findImportedModule (mkModuleName "TestPlugin") NoPkgQual
  lookupOrig md (mkTcOcc "TotalClass")

wantedCtToTotal :: Ct -> TcPluginM ((EvTerm, Ct), Ct)
wantedCtToTotal ct = do
  (targetClass, targetArgTy) <- case getClassPredTys_maybe $ ctPred ct of
    Just (cls, [ty]) -> do
      output "target cls:" cls
      output "target tyvar kind:" $ typeKind ty
      return (cls, typeKind ty)
    Just _ -> fail "Class has wrong arity"
    Nothing -> fail "Not a class constraint"
  let targetTyCon = classTyCon targetClass
  totalClass <- totalClassName >>= tcLookupClass
  output "totalClass:" totalClass
  let totalTyCon = classTyCon totalClass
  let predType = mkTyConApp totalTyCon [targetArgTy, mkTyConTy targetTyCon] 
  output "predType:" predType
  newCt <- mkNonCanonical <$> newWanted (ctLoc ct) predType
  let fakeEvTerm = EvExpr $ mkImpossibleExpr predType
  return ((fakeEvTerm, ct), newCt)

solve :: () -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solve () _ _ [] = do
  tcPluginIO $ putStrLn "asked to rewrite givens, doing nothing"
  return $ TcPluginSolveResult [] [] []
solve () _ _ wanteds = do
  output "wanteds:" wanteds
  let (maybeTotal, stillWanted) = partition canBeTotalCt wanteds
  output "Skipped (non-ADT args or >1 arg):" stillWanted
  (solvedCts, newCts) <- mapAndUnzipM wantedCtToTotal maybeTotal
  output "Adding TotalClass constraints:" newCts
  return $ TcPluginSolveResult 
    { tcPluginSolvedCts = solvedCts
    , tcPluginNewCts = newCts
    , tcPluginInsolubleCts = []
    }

output :: Outputable a => String -> a -> TcPluginM ()
output str x = tcPluginIO . putStrLn $ str ++ " " ++ showPprUnsafe x

