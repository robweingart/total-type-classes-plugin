module TestPlugin.Rewriter.Solve ( solveWithPlaceholder ) where 

import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc, mkNonCanonical, mkSimpleWC, ctEvidence, isSolvedWC)
import GHC.Tc.Types.Evidence (EvTerm)
import GHC.Core.Predicate (getClassPredTys_maybe)
import GHC.Core.Class (Class(classTyCon))
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Solver (solveWanteds)
import TestPlugin.Rewriter.Placeholder (mkPlaceholder)

totalClassName :: TcPluginM Name
totalClassName = do
  Found _ md <- findImportedModule (mkModuleName "TestPlugin") NoPkgQual
  lookupOrig md (mkTcOcc "TotalClass")

solveWithPlaceholder :: Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveWithPlaceholder ct
  | Just (targetClass, _) <- getClassPredTys_maybe $ ctPred ct = do
    totalClass <- totalClassName >>= tcLookupClass
    if targetClass == totalClass
    then return Nothing
    else do
      let targetTyConTy = mkTyConTy $ classTyCon targetClass
      let predType = mkTyConApp (classTyCon totalClass) [typeKind targetTyConTy, targetTyConTy] 
      newCt <- mkNonCanonical <$> newWanted (ctLoc ct) predType
      (wc, _) <- unsafeTcPluginTcM $ runTcS $ solveWanteds (mkSimpleWC [ctEvidence newCt])
      if isSolvedWC wc
      then return $ Just (mkPlaceholder predType, ct)
      else return Nothing
  | otherwise = return Nothing

