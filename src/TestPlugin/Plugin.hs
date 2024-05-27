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
import GHC.Tc.Types.Evidence (EvBindsVar, EvTerm)
import GHC.Tc.Types.Constraint (Ct, ctPred)
import GHC.Core.Predicate (getClassPredTys_maybe, getClassPredTys)
import GHC.Tc.Utils.Monad (getGblEnv)
import GHC.Data.Bag (filterBag)
import GHC (HsBindLR (FunBind, fun_id, PatBind, VarBind, PatSynBind, XHsBindsLR), GhcTc)

-- isRealFun :: HsBindLR GhcTc GhcTc -> Bool
-- isRealFun (FunBind {fun_id=(L _ var)}) = isInternalName (varName var)
-- isRealFun _ = False

plugin :: Plugin
plugin = defaultPlugin
  {  typeCheckResultAction = \_ _ tc -> do
    dFlags <- getDynFlags
   -- liftIO $ putStrLn $ showSDoc dFlags $ ppr $ tcg_inst_env tc
    gbl <- getGblEnv
    forM_ (tcg_binds gbl) $ \(L _ x) -> do
      liftIO $ putStr $ case x of
        FunBind {} -> "FunBind: "
        PatBind {} -> "PatBind: "
        VarBind {} -> "VarBind: "
        PatSynBind {} -> "PatSynBind: "
        XHsBindsLR _ -> "XHsBindsLR: "
      liftIO $ putStrLn $ showSDoc dFlags $ ppr x
    --let binds = filterBag (\(L _ x) ->  isRealFun x) (tcg_binds gbl)
    --liftIO $ putStrLn $ showSDoc dFlags $ ppr binds
    liftIO $ putStrLn $ showSDoc dFlags $ ppr $ tcg_ev_binds gbl
    return tc
  , tcPlugin = \_ -> Just $
    TcPlugin { tcPluginInit = return ()
    , tcPluginSolve = solve
    , tcPluginRewrite = const emptyUFM
    , tcPluginStop = \_ -> return ()
    }
  }

canBeTotal :: Class -> Bool
canBeTotal cls = all (isAlgType . varType) (classTyVars cls)

wantedCtToTotal :: Ct -> TcPluginM (EvTerm, Ct)
wantedCtToTotal ct = return undefined

solve :: () -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solve () _ _ [] = do
  tcPluginIO $ putStrLn "asked to rewrite givens, doing nothing"
  return $ TcPluginSolveResult [] [] []
solve () _ _ wanteds = do
  tcPluginIO $ putStrLn "asked to solve, doing nothing"
  let (maybeTotal, stillWanted) = partition (canBeTotal . fst . getClassPredTys . ctPred) wanteds
  output "Skipped (non-ADT args):" stillWanted
  totalCts <- mapM wantedCtToTotal maybeTotal
  output "Adding TotalClass constraints:" totalCts
  return $ TcPluginSolveResult [] totalCts []

output :: Outputable a => String -> a -> TcPluginM ()
output str x = tcPluginIO . putStrLn $ str ++ " " ++ showPprUnsafe x

-- lookupTotalClasses :: TcPluginM [Class]
-- lookupTotalClasses = do
--   Found _ md <- findImportedModule (mkModuleName "TestPlugin") NoPkgQual
--   totalClassName <- lookupOrig md (mkTcOcc "TotalClass")
--   (gbl_env, lcl_env) <- getEnvs
--   output $ tcg_tcs gbl_env
--   return []
