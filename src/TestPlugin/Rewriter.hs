module TestPlugin.Rewriter (totalTcResultAction) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcGblEnv(..), TcM)

import GHC.Tc.Solver (captureTopConstraints, simplifyTop)
import GHC.Tc.Utils.Monad (setGblEnv, restoreEnvs)
import GHC.Data.Bag (unionBags, Bag)
import GHC.Tc.Zonk.Type (zonkTopDecls)

import TestPlugin.Rewriter.Bind (rewriteBinds)
import TestPlugin.Rewriter.Call (rewriteCalls)
import TestPlugin.Rewriter.Utils (printLnTcM)
import GHC.Types.TypeEnv (plusTypeEnv)
import GHC.Tc.Types.Evidence (EvBind)

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ gbl = do
  printLnTcM  "totalTcResultAction {"
  ((gbl', lcl), lie) <- setGblEnv gbl $ captureTopConstraints $ rewriteBinds' (tcg_binds gbl)
  new_ev_binds <- restoreEnvs (gbl', lcl) $ simplifyTop lie
  gbl'' <- rezonk new_ev_binds gbl'
  printLnTcM  "}"
  return gbl''
  where
    rewriteBinds' binds = rewriteBinds binds rewriteCalls' 
    rewriteCalls' env binds = rewriteCalls env binds rewriteBinds'

rezonk :: Bag EvBind -> TcGblEnv -> TcM TcGblEnv
rezonk new_ev_binds gbl@(TcGblEnv{ tcg_binds     = binds
                                 , tcg_ev_binds  = ev_binds
                                 , tcg_imp_specs = imp_specs
                                 , tcg_rules     = rules
                                 , tcg_fords     = fords
                                 , tcg_type_env  = type_env})
  = setGblEnv gbl $ do
    (type_env', ev_binds', binds', fords', imp_specs', rules') <- zonkTopDecls (ev_binds `unionBags` new_ev_binds) binds rules imp_specs fords
    return $ gbl
      { tcg_binds     = binds'
      , tcg_ev_binds  = ev_binds'
      , tcg_imp_specs = imp_specs'
      , tcg_rules     = rules'
      , tcg_fords     = fords'
      , tcg_type_env  = type_env `plusTypeEnv` type_env'}
    
