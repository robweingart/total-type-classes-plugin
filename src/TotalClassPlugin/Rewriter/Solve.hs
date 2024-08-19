module TotalClassPlugin.Rewriter.Solve ( solveWithPlaceholder ) where 

import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc, mkNonCanonical, mkSimpleWC, ctEvidence, isSolvedWC)
import GHC.Tc.Types.Evidence (EvTerm)
import GHC.Core.Predicate (getClassPredTys_maybe)
import GHC.Core.Class (Class(classTyCon))
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Solver (solveWanteds)
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
  if isClassPred totalConstraint ct then return Nothing
  else do
    let predType = mkTyConApp (classTyCon totalConstraint) [ctPred ct]
    newCt <- mkNonCanonical <$> newWanted (ctLoc ct) predType
    (wc, _) <- unsafeTcPluginTcM $ runTcS $ solveWanteds (mkSimpleWC [ctEvidence newCt])
    if isSolvedWC wc
    then do 
      tcPluginIO $ putStrLn ("Inserting placeholder:" ++ showPprUnsafe predType)
      return $ Just (mkPlaceholder predType, ct)
    else solveWithPlaceholder' ct

solveWithPlaceholder' :: Ct -> TcPluginM (Maybe (EvTerm, Ct))
solveWithPlaceholder' ct
  | Just (targetClass, _) <- getClassPredTys_maybe $ ctPred ct = do
    tcPluginIO $ putStrLn ("Trying to solve:" ++ showPprUnsafe ct)
    totalClass <- lookupClassByName "TotalClass"
    if targetClass == totalClass
    then do
      tcPluginIO $ putStrLn ("This is TotalClass, skipping:" ++ showPprUnsafe targetClass)
      return Nothing
    else do
      let targetTyConTy = mkTyConTy $ classTyCon targetClass
      let predType = mkTyConApp (classTyCon totalClass) [typeKind targetTyConTy, targetTyConTy] 
      newCt <- mkNonCanonical <$> newWanted (ctLoc ct) predType
      (wc, _) <- unsafeTcPluginTcM $ runTcS $ solveWanteds (mkSimpleWC [ctEvidence newCt])
      if isSolvedWC wc
      then do 
        tcPluginIO $ putStrLn ("Inserting placeholder:" ++ showPprUnsafe predType)
        return $ Just (mkPlaceholder predType, ct)
      else return Nothing
  | otherwise = return Nothing

