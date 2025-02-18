module TotalClassPlugin.Rewriter.Solve (solveWithPlaceholder) where

import GHC.Core.Class (Class (classTyCon))
import GHC.Core.Predicate (getClassPredTys_maybe)
import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Solver (solveWanteds)
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Types.Constraint (Ct, ctEvidence, ctLoc, ctPred, isSolvedWC, mkNonCanonical, mkSimpleWC)
import GHC.Tc.Types.Evidence (EvTerm)
import TotalClassPlugin.Rewriter.Placeholder (mkPlaceholder)

lookupClassByName :: String -> TcPluginM Class
lookupClassByName str = do
  Found _ md <- findImportedModule (mkModuleName "TotalClassPlugin") NoPkgQual
  name <- lookupOrig md (mkTcOcc str)
  tcLookupClass name

isClassPred :: Class -> Ct -> Bool
isClassPred cls ct
  | Just (cls', _) <- getClassPredTys_maybe (ctPred ct) = cls == cls'
  | otherwise = False

solveWithPlaceholder :: Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveWithPlaceholder ct = do
  totalConstraint <- lookupClassByName "TotalConstraint"
  if isClassPred totalConstraint ct
    then return Nothing
    else do
      let predType = mkTyConApp (classTyCon totalConstraint) [ctPred ct]
      newCt <- mkNonCanonical <$> newWanted (ctLoc ct) predType
      (wc, _) <- unsafeTcPluginTcM $ runTcS $ solveWanteds (mkSimpleWC [ctEvidence newCt])
      if isSolvedWC wc
        then do
          -- tcPluginIO $ putStrLn ("Inserting placeholder:" ++ showPprUnsafe predType)
          return $ Just (mkPlaceholder predType, ct)
        else return Nothing
