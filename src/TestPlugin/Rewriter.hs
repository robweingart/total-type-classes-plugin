module TestPlugin.Rewriter (totalTcResultAction) where

import Data.Foldable (forM_)

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM, TcGblEnv (..))
import GHC.Tc.Types.Evidence (HsWrapper (..))
import GHC (LHsBindLR, GhcTc, HsBindLR (..), MatchGroup (..), MatchGroupTc (..), Match (..), AbsBinds (..), HsExpr (..), XXExprGhcTc (..), HsWrap (..))
import GHC.Tc.Utils.Monad (getGblEnv)

import Data.Generics (everywhereM, mkM)

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ tc = do
    gbl <- getGblEnv
    output' 0 "TcEvBinds: " $ tcg_ev_binds gbl 
    --_ <- everywhereM (mkM printWrapper') (tcg_binds gbl) 
    --_ <- everywhereM (mkM printVar) (tcg_binds gbl) 
    _ <- everywhereM (mkM printExpr) (tcg_binds gbl) 
    forM_ (tcg_binds gbl) (printInnerBinds 0)
    return tc

outputTcM :: Outputable a => String -> a -> TcM ()
outputTcM str x = do
  dFlags <- getDynFlags
  liftIO $ putStrLn $ str ++ showSDoc dFlags (ppr x)

output' :: Outputable a => Int -> String -> a -> TcM ()
output' n' str = outputTcM (replicate n' ' ' ++ str)

printWrapper :: Int -> HsWrapper -> TcM()
printWrapper n w@WpHole = output' n "Hole" w
printWrapper n w@(WpCompose l r) = do
  output' n "WpCompose" w
  printWrapper (n+1) l
  printWrapper (n+1) r
printWrapper n w@(WpFun {}) = output' n "WpFun" w
printWrapper n w@(WpCast _) = output' n "WpCast" w
printWrapper n w@(WpEvLam evvar) = do
  output' n "WpEvLam" w
  output' (n+1) "EvVar: " evvar
printWrapper n w@(WpEvApp evterm) = do
  output' n "WpEvApp" w
  output' (n+1) "EvTerm: " evterm
printWrapper n w@(WpTyLam tyvar) = do
  output' n "WpTyLam" w
  output' (n+1) "TyVar: " tyvar
printWrapper n w@(WpTyApp _) = output' n "WpTyApp" w
printWrapper n w@(WpLet evbinds) = do 
  output' n "WpLet" w
  output' (n+1) "TcEvBinds" evbinds
printWrapper n w@(WpMultCoercion _) = output' n "WpMultCoercion" w

printInnerBinds :: Int -> LHsBindLR GhcTc GhcTc -> TcM ()
printInnerBinds n (L _ b) = do
  case b of
    FunBind { fun_ext=ext, fun_id=fid, fun_matches=matches } -> do
      output' n "FunBind " ()
      output' n "ext: " ext
      printWrapper (n+1) ext
      output' n "id: " fid
      output' n "matches: " ()
      case matches of
        MG { mg_ext = (MatchGroupTc {mg_arg_tys=arg_tys, mg_res_ty=res_ty}), mg_alts=(L _ alts) } -> do
          output' (n+1) "arg_tys: " arg_tys
          output' (n+1) "res_ty: " res_ty
          output' (n+1) "alts: " ()
          forM_ alts $ \(L _ (Match {m_pats=pats, m_grhss=grhss})) -> do
            output' (n+2) "pats: " pats
            output' (n+2) "grhss: " ()

    XHsBindsLR (AbsBinds { abs_ev_vars=ev_vars, abs_binds=binds, abs_ev_binds=ev_binds }) -> do
      output' n "XHsBindsLR " ()
      output' n "ev_vars: " ev_vars
      output' n "ev_binds: " ev_binds
      output' n "binds: " binds
      forM_ binds $ printInnerBinds (n + 1)
    _ -> return ()


printWrapper' :: HsWrapper -> TcM HsWrapper
printWrapper' w@(WpEvApp term) = do
  outputTcM "evterm: " term
  return w
printWrapper' w = return w

printVar :: Var -> TcM Var
printVar var = do
  outputTcM "var: " var
  return var

printExpr :: HsExpr GhcTc -> TcM (HsExpr GhcTc)
printExpr expr@(HsApp _ f x) = do
  outputTcM "f: " f
  outputTcM "x: " x
  return expr
printExpr expr@(XExpr (WrapExpr (HsWrap w e))) = do
  outputTcM "wrapper: " w
  printWrapper 1 w
  outputTcM "wrapped expr:" e
  return expr
printExpr expr@(HsVar _ i) = do
  --outputTcM "var id: " i
  --outputTcM "var type: " $ varType $ unLoc i
  return expr
printExpr expr = do 
  -- outputTcM "expr: " expr
  return expr

