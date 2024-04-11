module TestPlugin.Plugin ( plugin ) where

import Control.Monad.IO.Class
import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types

printAndReturn :: (MonadIO m) => String -> a -> m a
printAndReturn str input = do
  liftIO $ putStrLn str
  return input

plugin :: Plugin
plugin = defaultPlugin
  {  parsedResultAction = \_ _ -> printAndReturn "parsedResultAction"
  ,  renamedResultAction = \_ tc gr -> do
    liftIO $ putStrLn "renamedResultAction"
    return (tc, gr)
  ,  typeCheckResultAction = \_ _ tc -> do
    dFlags <- getDynFlags
    liftIO $ putStrLn $ showSDoc dFlags $ ppr $ tcg_inst_env tc
    return tc
  ,  spliceRunAction = \_ -> printAndReturn "spliceRunAction"
  --,  interfaceLoadAction = \_ -> printAndReturn "interfaceLoadAction"
  , tcPlugin = \_ -> Just $
    TcPlugin { tcPluginInit = tcPluginIO $ putStrLn "tcPluginInit"
    , tcPluginSolve = \() _ _ _ -> return $ TcPluginSolveResult [] [] []
    , tcPluginRewrite = \() -> emptyUFM
    , tcPluginStop = \() -> return ()
    }
  }

