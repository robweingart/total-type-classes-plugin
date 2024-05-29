{-# LANGUAGE LambdaCase #-}

module TestPlugin.Plugin ( plugin ) where

import Data.List (partition)
import Data.Foldable (forM_)
import Control.Monad.IO.Class
import GHC.Core.Class
import qualified GHC.Core.InstEnv as InstEnv
import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Evidence (EvBindsVar, EvTerm (EvExpr))
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc, mkNonCanonical)
import GHC.Core.Predicate (getClassPredTys_maybe, getClassPredTys, classifyPredType, Pred (ClassPred))
import GHC.Tc.Utils.Monad (getGblEnv, mapAndUnzipM)
import GHC.Data.Bag (filterBag)
import GHC (HsBindLR (FunBind, fun_id, PatBind, VarBind, PatSynBind, XHsBindsLR), GhcTc, AbsBinds (AbsBinds, abs_ev_vars, abs_binds))

-- isRealFun :: HsBindLR GhcTc GhcTc -> Bool
-- isRealFun (FunBind {fun_id=(L _ var)}) = isInternalName (varName var)
-- isRealFun _ = False

outputTcM :: Outputable a => DynFlags -> String -> a -> TcM ()
outputTcM dFlags str x = liftIO $ putStrLn $ str ++ showSDoc dFlags (ppr x)

plugin :: Plugin
plugin = defaultPlugin
  {  typeCheckResultAction = \_ _ tc -> do
    dFlags <- getDynFlags
   -- liftIO $ putStrLn $ showSDoc dFlags $ ppr $ tcg_inst_env tc
    gbl <- getGblEnv
    forM_ (tcg_binds gbl) $ \(L _ x) -> (case x of
        --XHsBindsLR (AbsBinds {abs_ev_vars=ev_vars, abs_binds=binds}) -> do
        --  outputTcM dFlags "XHsBindsLR: " x
        --  outputTcM dFlags "ev_vars: " ev_vars
        --  outputTcM dFlags "binds: " binds
        _ -> return ())
    --let binds = filterBag (\(L _ x) ->  isRealFun x) (tcg_binds gbl)
    --liftIO $ putStrLn $ showSDoc dFlags $ ppr binds
    --outputTcM dFlags $ tcg_ev_binds gbl
    return tc
  , tcPlugin = \_ -> Just $
    TcPlugin { tcPluginInit = return ()
    , tcPluginSolve = solve
    , tcPluginRewrite = const emptyUFM
    , tcPluginStop = \_ -> return ()
    }
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
  -- case classifyPredType predType of
  --   ClassPred cls tys -> do
  --     output "cls:" cls
  --     output "tys:" tys
  --   _ -> return ()
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

-- lookupTotalClasses :: TcPluginM [Class]
-- lookupTotalClasses = do
--   Found _ md <- findImportedModule (mkModuleName "TestPlugin") NoPkgQual
--   totalClassName <- lookupOrig md (mkTcOcc "TotalClass")
--   (gbl_env, lcl_env) <- getEnvs
--   output $ tcg_tcs gbl_env
--   return []
