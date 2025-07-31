module TotalClassPlugin.Rewriter.Solve (solveWithPlaceholder) where

import GHC.Core.Class (Class (classTyCon))
import GHC.Core.Predicate (getClassPredTys_maybe)
import GHC.Plugins
import GHC.Stack (emptyCallStack)
import GHC.Tc.Plugin
import GHC.Tc.Solver (solveWanteds)
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Types.Constraint (Ct, ctEvidence, ctLoc, ctPred, isSolvedWC, mkImplicWC, mkNonCanonical, mkSimpleWC)
import GHC.Tc.Types.Evidence (EvTerm)
import GHC.Tc.Types.Origin (SkolemInfoAnon (UnkSkol))
import GHC.Tc.Utils.Monad (getTcLevel)
import GHC.Tc.Utils.TcMType (newEvVars)
import GHC.Tc.Utils.Unify (buildImplicationFor)
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

solveWithPlaceholder :: [Ct] -> Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveWithPlaceholder givens ct = do
  totalConstraint <- lookupClassByName "TotalConstraint"
  if isClassPred totalConstraint ct
    then return Nothing
    else do
      let predType = mkTyConApp (classTyCon totalConstraint) [ctPred ct]
      wantedCt <- mkNonCanonical <$> newWanted (ctLoc ct) predType
      (wc, _) <- unsafeTcPluginTcM $ do
        tc_level <- getTcLevel
        given_vars <- newEvVars (map ctPred givens)
        (implications, _) <- buildImplicationFor tc_level (UnkSkol emptyCallStack) [] given_vars (mkSimpleWC [ctEvidence wantedCt])
        runTcS $ solveWanteds (mkImplicWC implications)
      if isSolvedWC wc
        then do
          return $ Just (mkPlaceholder predType, ct)
        else return Nothing
