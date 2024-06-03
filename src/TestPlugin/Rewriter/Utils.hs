{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter.Utils (outputTcM, printWrapper, printBndrTys) where

import Data.Foldable (forM_)

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM)
import GHC.Tc.Types.Evidence (HsWrapper (..), EvBind(EvBind), TcEvBinds (TcEvBinds, EvBinds), EvTerm (EvExpr))
import GHC.Core.TyCo.Rep (Type(..), TyCoBinder (Named, Anon), Scaled (Scaled))


printBndrTys :: Type -> TcM ()
printBndrTys ty = do
  let (bndrs, ty') = splitInvisPiTys ty
  outputTcM "bndrs: " bndrs
  outputTcM "ty without bndrs: " ty'
  case ty' of
    FunTy _ _ (TyConApp _ [_, TyVarTy tyVar]) _ -> outputTcM "Ty var in arg: " $ varUnique tyVar
    _ -> return ()
  forM_ bndrs $ \case
    Named (Bndr var _) -> outputTcM "ty var in bndr: " $ varUnique var
    --Anon _ arg -> outputTcM "anon bndr: " arg
    Anon _ (Scaled _ (TyConApp _ [TyVarTy var])) -> outputTcM "ty var in bndr app: " $ varUnique var
    _ -> return ()

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
  case evterm of
    EvExpr expr -> do
      output' (n+1) "EvTerm type: " $ exprType expr
      case exprType expr of
        TyConApp _ [TyVarTy var] -> output' (n+1) "var: " $ varUnique var
        _ -> return ()
    _ -> return ()
printWrapper n w@(WpTyLam tyvar) = do
  output' n "WpTyLam" w
  output' (n+1) "TyVar: " $ varUnique tyvar
printWrapper n w@(WpTyApp t) = do
  output' n "WpTyApp" w
  output' (n+1) "type: " t
  case t of
    TyVarTy var -> output' (n+1) "var: " $ varUnique var
    _ -> return ()
printWrapper n w@(WpLet evbinds) = do 
  output' n "WpLet" w
  output' (n+1) "TcEvBinds: " ()
  case evbinds of
    TcEvBinds _ -> return ()
    EvBinds binds -> forM_ binds $ \(EvBind lhs rhs _) -> do
      output' (n+2) "LHS: " lhs
      output' (n+3) "type: " $ varType lhs
      case varType lhs of
        TyConApp _ [TyVarTy var] -> output' (n+3) "var: " $ varUnique var
        _ -> return ()
      output' (n+3) "RHS: " rhs
printWrapper n w@(WpMultCoercion _) = output' n "WpMultCoercion" w
