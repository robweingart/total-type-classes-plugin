{-# LANGUAGE LambdaCase #-}

module TotalClassPlugin.Rewriter.Utils (withTcRef, printLnTcM, outputTcM, outputFullTcM, failTcM, printWrapper, printBndrTys) where

import Data.Data (Data)
import Data.Foldable (forM_)
import GHC.Core.TyCo.Rep (Scaled (Scaled), Type (..))
import GHC.Data.Bag (Bag)
import GHC.Hs.Dump (BlankEpAnnotations (BlankEpAnnotations), BlankSrcSpan (BlankSrcSpan), showAstData)
import GHC.Plugins
import GHC.Tc.Errors.Types (TcRnMessage (TcRnUnknownMessage))
import GHC.Tc.Types (TcM, TcRef)
import GHC.Tc.Types.Evidence (EvBind (EvBind), EvBindsVar (CoEvBindsVar, EvBindsVar, ebv_binds, ebv_tcvs), EvTerm (EvExpr), HsWrapper (..), TcEvBinds (EvBinds, TcEvBinds), evBindMapBinds)
import GHC.Tc.Utils.Monad (failWith, newTcRef, readTcRef)
import GHC.Tc.Utils.TcType (evVarPred)
import GHC.Types.Error (mkSimpleUnknownDiagnostic)
import GHC.Utils.Error (mkPlainError)

withTcRef :: a -> (TcRef a -> TcM r) -> TcM (a, r)
withTcRef initial f = do
  ref <- newTcRef initial
  result <- f ref
  final <- readTcRef ref
  return (final, result)

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
    Anon (Scaled _ (TyConApp _ [TyVarTy var])) _ -> outputTcM "ty var in bndr app: " $ varUnique var
    _ -> return ()

printLnTcM :: String -> TcM ()
printLnTcM = liftIO . putStrLn

outputTcM :: (Outputable a) => String -> a -> TcM ()
outputTcM str x = do
  dFlags <- getDynFlags
  liftIO $ putStrLn $ str ++ showSDoc dFlags (ppr x)

outputFullTcM :: (Data a) => String -> a -> TcM ()
outputFullTcM str x = do
  dFlags <- getDynFlags
  liftIO $ putStrLn $ str ++ showSDoc dFlags (showAstData BlankSrcSpan BlankEpAnnotations x)

failTcM :: SDoc -> TcM a
failTcM doc = failWith $ TcRnUnknownMessage $ mkSimpleUnknownDiagnostic $ mkPlainError [] doc

output' :: (Outputable a) => Int -> String -> a -> TcM ()
output' n' str = outputTcM (replicate n' ' ' ++ str)

printWrapper :: Int -> HsWrapper -> TcM ()
printWrapper n w@WpHole = output' n "Hole" w
printWrapper n w@(WpCompose l r) = do
  output' n "WpCompose" w
  printWrapper (n + 1) l
  printWrapper (n + 1) r
printWrapper n w@(WpFun l r arg) = do
  output' n "WpFun" w
  output' (n + 1) "arg: " arg
  printWrapper (n + 1) l
  printWrapper (n + 1) r
printWrapper n w@(WpCast co) = do
  output' n "WpCast" w
  output' (n + 1) "coercion: " co
printWrapper n w@(WpEvLam evvar) = do
  output' n "WpEvLam" w
  output' (n + 1) "EvVar: " evvar
  output' (n + 1) "EvVar type: " $ evVarPred evvar
  case evVarPred evvar of
    TyConApp _ [TyVarTy var] -> output' (n + 1) "var: " $ varUnique var
    _ -> return ()
printWrapper n w@(WpEvApp evterm) = do
  output' n "WpEvApp" w
  output' (n + 1) "EvTerm: " evterm
  case evterm of
    EvExpr expr -> do
      output' (n + 1) "EvTerm type: " $ exprType expr
      case exprType expr of
        TyConApp _ [TyVarTy var] -> output' (n + 1) "var: " $ varUnique var
        _ -> return ()
    _ -> return ()
printWrapper n w@(WpTyLam tyvar) = do
  output' n "WpTyLam" w
  output' (n + 1) "TyVar: " $ varUnique tyvar
printWrapper n w@(WpTyApp t) = do
  output' n "WpTyApp" w
  output' (n + 1) "type: " t
  case t of
    TyVarTy var -> output' (n + 1) "var: " $ varUnique var
    _ -> return ()
printWrapper n w@(WpLet ev_binds) = do
  output' n "WpLet" w
  case ev_binds of
    TcEvBinds (CoEvBindsVar {ebv_tcvs = tcvs}) -> readTcRef tcvs >>= output' (n + 1) "TcEvBinds CoEvBindsVar: "
    TcEvBinds (EvBindsVar {ebv_binds = binds}) -> do
      output' (n + 1) "TcEvBinds EvBindsVar: " ()
      ebs <- readTcRef binds
      printEvBinds (n + 2) $ evBindMapBinds ebs
    EvBinds ebm -> do
      output' (n + 1) "EvBinds: " ()
      printEvBinds (n + 2) ebm
printWrapper n w@(WpMultCoercion _) = output' n "WpMultCoercion" w

printEvBinds :: Int -> Bag EvBind -> TcM ()
printEvBinds n binds = do
  forM_ binds $ \(EvBind lhs rhs _) -> do
    output' (n + 2) "LHS: " lhs
    output' (n + 3) "type: " $ varType lhs
    case varType lhs of
      TyConApp _ [TyVarTy var] -> output' (n + 3) "var: " $ varUnique var
      _ -> return ()
    output' (n + 3) "RHS: " rhs
