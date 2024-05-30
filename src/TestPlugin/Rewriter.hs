{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter (totalTcResultAction) where

import Data.Foldable (forM_)

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM, TcGblEnv (..))
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (EvBind, eb_lhs, eb_rhs), TcEvBinds (TcEvBinds, EvBinds), EvTerm (EvExpr))
import GHC (LHsBindLR, GhcTc, HsBindLR (..), MatchGroup (..), MatchGroupTc (..), Match (..), AbsBinds (..), HsExpr (..), XXExprGhcTc (..), HsWrap (..))
import GHC.Tc.Utils.Monad (getGblEnv, mapMaybeM)

import Data.Generics (everywhereM, mkM, mkT, somewhere, everywhere)
import Control.Monad.State (StateT (runStateT), MonadTrans (lift), modify, when, unless)
import GHC.Data.Bag (filterBagM)
import TestPlugin.Placeholder (isPlaceholder, getPlaceholderPredType)
import GHC.Tc.Utils.TcType (mkPhiTy)
import GHC.Core.TyCo.Rep (Type(TyVarTy, AppTy, TyConApp, CoercionTy, CastTy), TyCoBinder (Named, Anon), Scaled (Scaled))
import GHC.Hs.Syn.Type (hsExprType)
import Data.Maybe (mapMaybe, fromMaybe)

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ gbl = do
    -- _ <- everywhereM (mkM printWrapper') (tcg_binds gbl) 
    --_ <- everywhereM (mkM printType) (tcg_binds gbl) 
    --_ <- everywhereM (mkM printVar) (tcg_binds gbl) 
    --_ <- everywhereM (mkM printUnique) (tcg_binds gbl) 
    --_ <- everywhereM (mkM printExpr) (tcg_binds gbl) 
    forM_ (tcg_binds gbl) (printInnerBinds 0)
    (binds', ids) <- runStateT (everywhereM (mkM rewriteHsBindLR) (tcg_binds gbl)) emptyVarSet
    outputTcM "modified ids: " ids
    return gbl {tcg_binds = binds'}

type TcStateM s a = StateT s TcM a

rewriteHsBindLR :: HsBindLR GhcTc GhcTc -> TcStateM IdSet (HsBindLR GhcTc GhcTc)
rewriteHsBindLR b@(FunBind {fun_id=(L loc fid), fun_ext=wrapper }) = do
  lift $ outputTcM "fun type: " $ varType fid
  result <- lift $ rewriteHsWrapper wrapper
  case result of
    Nothing -> do
      lift $ outputTcM "var info for normal fun: " ()
      let (bndrs, ty) = splitInvisPiTys (varType fid)
      lift $ outputTcM "bndrs: " bndrs
      lift $ outputTcM "ty without bndrs: " ty
      forM_ bndrs $ \case
        Named (Bndr var _) -> lift $ outputTcM "ty var in bndr: " $ varUnique var
        --Anon _ arg -> lift $ outputTcM "anon bndr: " arg
        Anon _ (Scaled _ (TyConApp _ [TyVarTy var])) -> lift $ outputTcM "ty var in bndr app: " $ varUnique var
        _ -> return ()
      --newTy <- lift $ updateFunType (varType fid) []
      --lift $ outputTcM "type after adding []: " newTy
      return b
    Just (wrapper', newArgTys) -> do
      
      lift $ outputTcM "modifying fun: " fid
      modify (`extendVarSet` fid)
      lift $ outputTcM "old type: " $ varType fid
      newTy <- lift $ updateFunType (varType fid) (wrapperBinders wrapper) newArgTys
      lift $ outputTcM "new type: " newTy
      let fid' = setVarType fid newTy
      lift $ printWrapper 0 wrapper'
      return b {fun_id=L loc fid', fun_ext=wrapper'}
rewriteHsBindLR b = return b

wrapperBinders :: HsWrapper -> [Var]
wrapperBinders (WpCompose w1 w2) = wrapperBinders w1 ++ wrapperBinders w2
wrapperBinders (WpTyLam var) = [var]
wrapperBinders (WpEvLam var) = [var]
wrapperBinders _ = []

rewriteHsWrapper :: HsWrapper -> TcM (Maybe (HsWrapper, [PredType]))
rewriteHsWrapper wrapper = do
  (wrapper', evVars) <- runStateT (everywhereM (mkM rewriteTcEvBinds) wrapper) [] 
  outputTcM "ev vars to process: " evVars
  outputTcM "ev var types: " $ varType <$> evVars
  case evVars of
    [] -> return Nothing
    evVars' -> do
      let (wrapper'', success) = addEvLams wrapper' evVars'
      unless success $ fail "Could not add new WpEvLams"
      return $ Just (wrapper'', varType <$> evVars')

rewriteTcEvBinds :: TcEvBinds -> TcStateM [EvVar] TcEvBinds
rewriteTcEvBinds (TcEvBinds _) = fail "Encountered unzonked TcEvBinds, this should not happen"
rewriteTcEvBinds (EvBinds binds) = do
  binds' <- filterBagM isNotPlaceholder binds
  return $ EvBinds binds'

isNotPlaceholder :: EvBind -> TcStateM [EvVar] Bool
isNotPlaceholder (EvBind {eb_lhs=evVar, eb_rhs=evTerm})
  | Just predType <- getPlaceholderPredType evTerm = do
    case varType evVar of
      TyConApp _ [TyVarTy var] -> lift $ outputTcM "ty var in placeholder lhs: " $ varUnique var
      _ -> return ()
    case predType of
      TyConApp _ [TyVarTy var] -> lift $ outputTcM "ty var in placeholder rhs: " $ varUnique var
      _ -> return ()
    modify (evVar :)
    return False
  | otherwise = return True

addEvLams :: HsWrapper -> [EvVar] -> (HsWrapper, Bool)
addEvLams (WpCompose w1 w2) vars = if done1 then (w1' <.> w2, done1) else (w1' <.> w2', done2) 
  where
    (w1', done1) = addEvLams w1 vars
    (w2', done2) = addEvLams w2 vars
--addEvLams w@(WpEvLam _) vars = (foldr ((<.>) . WpEvLam) w vars, True)
addEvLams w@(WpLet _) vars = (foldr ((<.>) . WpEvLam) w vars, True)
addEvLams w _ = (w, False)
--addEvLams wrapper vars = do
--  outputTcM "Input wrapper: " ()
--  printWrapper 1 wrapper
--  everywhereM (mkM addHere) wrapper
--  where
--    addHere :: HsWrapper -> TcM HsWrapper
--    addHere w@(WpLet _) = do
--      outputTcM "Adding binders to WpLet" ()
--      printWrapper 1 w
--      return $ foldr ((<.>) . WpEvLam) w vars
--    addHere w = return w

updateFunType :: Type -> [Var] -> [PredType] -> TcM Type
updateFunType ty wrapper_vars predTys = do
  --forM_ predTys $ \case
  --  --predTy -> outputTcM "pred: " predTy
  --  --AppTy _ y -> outputTcM "ty var in pred: " y
  --  TyConApp _ [TyVarTy var] -> outputTcM "ty var in pred: " $ varUnique var
  --  _ -> return ()
  --forM_ bndrs $ \case
  --  Named (Bndr var _) -> outputTcM "ty var in bndr: " $ varUnique var
  --  _ -> return ()
  let predTys' = everywhere (mkT tyVarFor) predTys 
  return $ mkPiTys bndrs $ mkPhiTy predTys' ty'
  where
    (bndrs, ty') = splitInvisPiTys ty
    ty_vars = mapMaybe (\case { Named (Bndr var _) -> Just var; _ -> Nothing }) bndrs
    var_pairs = zip wrapper_vars ty_vars
    tyVarFor var = fromMaybe var (lookup var var_pairs)






printBndrTys :: Type -> TcM ()
printBndrTys ty = do
  let (bndrs, ty') = splitInvisPiTys ty
  outputTcM "bndrs: " bndrs
  outputTcM "ty without bndrs: " ty'
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

printInnerBinds :: Int -> LHsBindLR GhcTc GhcTc -> TcM ()
printInnerBinds n (L _ b) = do
  case b of
    FunBind { fun_ext=ext, fun_id=fid, fun_matches=matches } -> do
      output' n "FunBind " ()
      output' n "ext: " ext
      printWrapper (n+1) ext
      output' n "id: " fid
      printBndrTys (varType $ unLoc fid)
      output' n "matches: " ()
      --case matches of
      --  MG { mg_ext = (MatchGroupTc {mg_arg_tys=arg_tys, mg_res_ty=res_ty}), mg_alts=(L _ alts) } -> do
      --    output' (n+1) "arg_tys: " arg_tys
      --    output' (n+1) "res_ty: " res_ty
      --    output' (n+1) "alts: " ()
      --    forM_ alts $ \(L _ (Match {m_pats=pats, m_grhss=grhss})) -> do
      --      output' (n+2) "pats: " pats
      --      output' (n+2) "grhss: " ()

    XHsBindsLR (AbsBinds { abs_ev_vars=ev_vars, abs_binds=binds, abs_ev_binds=ev_binds }) -> do
      output' n "XHsBindsLR " ()
      output' n "ev_vars: " ev_vars
      output' n "ev_binds: " ev_binds
      output' n "binds: " binds
      forM_ binds $ printInnerBinds (n + 1)
    _ -> return ()

printType :: Type -> TcM Type
printType t@(CastTy t' c) = do
  outputTcM "cast type: " t'
  outputTcM "cast coercion: " c
  return t
printType t@(CoercionTy c) = do
  outputTcM "coercion: " c
  return t
printType t = return t

printWrapper' :: HsWrapper -> TcM HsWrapper
printWrapper' w@(WpEvApp term) = do
  outputTcM "evterm: " term
  case term of
    EvExpr expr -> case expr of
      Var var -> do
        outputTcM "type: " $ varType var
        case varType var of
          TyConApp _ args -> outputTcM "var: " $ args
          _ -> return ()
      _ -> return ()
    _ -> return ()
  return w
printWrapper' w = return w

printVar :: TyCoVar -> TcM TyCoVar
printVar var = do
  outputTcM "var: " var
  outputTcM "var unique: " $ varUnique var
  return var

printUnique :: Unique -> TcM Unique
printUnique u = do
  outputTcM "unique: " u
  return u

printExpr :: HsExpr GhcTc -> TcM (HsExpr GhcTc)
printExpr expr@(HsApp _ f x) = do
  outputTcM "f: " f
  outputTcM "x: " x
  outputTcM "x type: " $ hsExprType (unLoc x)
  case hsExprType (unLoc x) of
    TyConApp _ [_, TyVarTy var] -> outputTcM "x var: " $ varUnique var
    _ -> return ()
  return expr
printExpr expr@(XExpr (WrapExpr (HsWrap w e))) = do
  outputTcM "wrapper: " ()
  printWrapper 0 w
  _ <- everywhereM (mkM printWrapper') w
  outputTcM "wrapped expr:" e
  outputTcM "wrapped expr type:" $ hsExprType e
  printBndrTys (hsExprType e)
  return expr
printExpr expr = do 
  -- outputTcM "expr: " expr
  return expr

