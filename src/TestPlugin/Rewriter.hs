{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter (totalTcResultAction) where

import Data.Foldable (forM_, Foldable (toList))

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcTyThing (AGlobal))
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (EvBind, eb_lhs, eb_rhs), TcEvBinds (TcEvBinds, EvBinds), EvTerm (EvExpr), EvBindMap, evBindMapBinds)
import GHC (LHsBindLR, GhcTc, HsBindLR (..), AbsBinds (..), HsExpr (..), XXExprGhcTc (..), HsWrap (..), LHsBinds, Ghc, ABExport (abe_mono, abe_poly, ABE, abe_wrap), TyThing (AnId))
import Data.Generics (everywhereM, mkM, mkT, everywhere)
import Control.Monad.State (StateT (runStateT), MonadTrans (lift), get, modify, when, unless, put, State, runState)
import GHC.Data.Bag (filterBagM, unionBags, Bag)
import TestPlugin.Placeholder (isPlaceholder)
import GHC.Tc.Utils.TcType (mkPhiTy)
import GHC.Core.TyCo.Rep (Type(TyVarTy, TyConApp, CoercionTy, CastTy), TyCoBinder (Named, Anon), Scaled (Scaled))
import GHC.Hs.Syn.Type (hsExprType)
import Data.Maybe (mapMaybe, fromMaybe, isJust)
import GHC.Tc.Utils.Monad (captureConstraints, setGblEnv, getGblEnv)
import GHC.Tc.Utils.Env (tcLookup, setGlobalTypeEnv, tcExtendGlobalEnv, tcExtendGlobalEnvImplicit)
import GHC.Types.TypeEnv (extendTypeEnv, extendTypeEnvWithIds)
import GHC.Types.Unique.DFM (plusUDFM)
import GHC.Tc.Utils.Instantiate (instCallConstraints)
import GHC.Tc.Types.Origin (CtOrigin(OccurrenceOf))
import GHC.Tc.Solver (solveWanteds)
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Types.Constraint (isSolvedWC, WantedConstraints, isEmptyWC)

type NameData = DNameEnv (Id, [PredType])

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ gbl = do
  forM_ (tcg_binds gbl) (printInnerBinds 0)
  --outputTcM "type env: " $ tcg_type_env gbl
  gbl' <- rewriteBinds gbl
  setGblEnv gbl' $ do
    typeEnv <- tcg_type_env <$> getGblEnv
    outputTcM "Final type env: " $ typeEnv
    forM_ (nonDetNameEnvElts typeEnv) $ \case
      AnId resId -> do
        outputTcM "env var: " $ resId
        outputTcM "env unique: " $ varUnique resId
        outputTcM "env type: " $ varType resId
      _ -> return ()
    --forM_ allIds $ \(var, _) -> do
    --  outputTcM "lookup var: " $ var
    --  outputTcM "lookup unique: " $ varUnique var
    --  res <- tcLookup (varName var)
    --  case res of
    --    AGlobal (AnId resId) -> do
    --      outputTcM "lookup type: " $ varType resId
    --    _ -> return ()
    getGblEnv

rewriteIdTypes :: NameData -> Id -> Id
rewriteIdTypes ids id'
  | Just (id'', _) <- lookupDNameEnv ids (varName id') = id''
  | otherwise = id'

rewriteBinds :: TcGblEnv -> TcM TcGblEnv
rewriteBinds gbl = do
  let binds = tcg_binds gbl
  (binds', newIds) <- runStateT (everywhereM (mkM rewriteHsBindLR) binds) emptyDNameEnv
  forM_ newIds $ \(id', _) -> do
   outputTcM "Modified id: " id'
   outputTcM "Modified id type: " $ varType id'
   outputTcM "Modified id unique: " $ varUnique id'
   return ()
  setGblEnv gbl{tcg_binds = binds'} $ tcExtendGlobalEnvImplicit (AnId . fst <$> toList newIds) $ do
    gbl' <- getGblEnv
    gbl'' <- rewriteCalls newIds gbl'
    setGblEnv gbl'' $ do
      forM_ newIds $ \(var, _) -> do
        outputTcM "lookup' var: " $ var
        outputTcM "lookup' unique: " $ varUnique var
        res <- tcLookup (varName var)
        case res of
          AGlobal (AnId resId) -> do
            outputTcM "lookup' type: " $ varType resId
          _ -> return ()
      getGblEnv


rewriteCalls :: NameData -> TcGblEnv -> TcM TcGblEnv
rewriteCalls ids gbl
  | isEmptyDNameEnv ids = return gbl
  | otherwise = do
    binds' <- everywhereM (mkM (rewriteCallsInBind ids)) (tcg_binds gbl)
    setGblEnv gbl{tcg_binds = binds'} $ do
      gbl' <- getGblEnv
      rewriteBinds gbl'

type TcStateM s a = StateT s TcM a

rewriteHsBindLR :: HsBindLR GhcTc GhcTc -> TcStateM NameData (HsBindLR GhcTc GhcTc)
rewriteHsBindLR (XHsBindsLR ab@(AbsBinds {abs_exports=exports, abs_binds=inner_binds})) = do
  prevIds <- get
  put emptyDNameEnv
  inner_binds' <- everywhereM (mkM rewriteInnerHsBindLR) inner_binds
  exports' <- mapM rewriteABExport exports
  newIds <- get
  --lift $ outputTcM "newly added: " newIds
  put (plusUDFM prevIds newIds)
  return $ XHsBindsLR ab{abs_binds=inner_binds',abs_exports=exports'}
rewriteHsBindLR b = return b

--rewriteABExport :: ABExport -> TcStateM NameData ABExport
--rewriteABExport e@ABE{abe_mono=mono, abe_poly=poly, abe_wrap=wrap} = do
--  modified <- get
--  case (lookupDNameEnv modified (varName mono), wrap) of
--    (Nothing, _) -> return e
--    (Just (newId, predTys), WpHole) -> do
--      unless (varName mono == varName newId) $ fail "unexpected mono id"
--      let new_mono = setVarType mono (varType newId)
--      let new_poly = setVarType poly (varType newId)
--      modify (\env -> extendDNameEnv env (varName new_poly) (new_poly, predTys))
--      return e{abe_mono=new_mono,abe_poly=new_poly}
--    (Just _, _) -> fail "modification occurred inside nontrivial ABE wrapper"

rewriteABExport :: ABExport -> TcStateM NameData ABExport
rewriteABExport e@ABE{abe_mono=mono, abe_poly=poly, abe_wrap=wrap} = do
  modified <- get
  if isEmptyDNameEnv modified then return e else do
    case lookupDNameEnv modified (varName mono) of
      Nothing -> return e
      Just (newMono, predTys) -> do
        let newPoly = setVarType poly (varType newMono)
        lift $ outputTcM "new_mono: " $ varType newMono
        modify (\env -> delFromDNameEnv env (varName mono))
        modify (\env -> extendDNameEnv env (varName poly) (newPoly, predTys))
        lift $ outputTcM "new_poly: " $ varType newPoly
        modified' <- get
        lift $ outputTcM "new_poly (actual): " $ fst <$> lookupDNameEnv modified' (varName poly)
        return e{abe_mono=newMono,abe_poly=newPoly}

rewriteInnerHsBindLR :: HsBindLR GhcTc GhcTc -> TcStateM NameData (HsBindLR GhcTc GhcTc)
rewriteInnerHsBindLR b@(FunBind {fun_id=(L loc fid), fun_ext=wrapper }) = do
  result <- lift $ rewriteHsWrapper wrapper
  case result of
    Nothing -> return b
    Just (wrapper', newArgTys) -> do
      newTy <- lift $ updateFunType (varType fid) (wrapperBinders wrapper) newArgTys
      let fid' = setVarType fid newTy
      modify (\env -> extendDNameEnv env (varName fid') (fid', newArgTys))
      return b {fun_id=L loc fid', fun_ext=wrapper'}
rewriteInnerHsBindLR b = return b

wrapperBinders :: HsWrapper -> [Var]
wrapperBinders (WpCompose w1 w2) = wrapperBinders w1 ++ wrapperBinders w2
wrapperBinders (WpTyLam var) = [var]
wrapperBinders _ = []

rewriteHsWrapper :: HsWrapper -> TcM (Maybe (HsWrapper, [PredType]))
rewriteHsWrapper wrapper = do
  (wrapper', tys) <- runStateT (everywhereM (mkM rewriteWpLet) wrapper) [] 
  case tys of
    [] -> return Nothing
    [[]] -> return Nothing
    [newArgTys] -> return $ Just (wrapper', newArgTys) 
    _ -> fail "encountered multiple WpLet, this should not happen"

rewriteWpLet :: HsWrapper -> TcStateM [[PredType]] HsWrapper
rewriteWpLet (WpLet (TcEvBinds _)) = fail "Encountered unzonked TcEvBinds, this should not happen"
rewriteWpLet (WpLet (EvBinds binds)) = do
  let (binds', evVars) = runState (filterBagM isNotPlaceholder binds) []
  modify ((varType <$> evVars) :)
  return $ foldr ((<.>) . WpEvLam) (WpLet (EvBinds binds')) evVars
rewriteWpLet w = return w

isNotPlaceholder :: EvBind -> State [EvVar] Bool
isNotPlaceholder (EvBind {eb_lhs=evVar, eb_rhs=evTerm})
  | isPlaceholder evTerm = do
    modify (evVar :)
    return False
  | otherwise = return True

updateFunType :: Type -> [Var] -> [PredType] -> TcM Type
updateFunType ty wrapper_vars predTys = do
  let predTys' = everywhere (mkT tyVarFor) predTys 
  return $ mkPiTys bndrs $ mkPhiTy predTys' ty'
  where
    (bndrs, ty') = splitInvisPiTys ty
    ty_vars = mapMaybe (\case { Named (Bndr var _) -> Just var; _ -> Nothing }) bndrs
    var_pairs = zip wrapper_vars ty_vars
    tyVarFor var = fromMaybe var (lookup var var_pairs)

rewriteCallsInBind :: NameData -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteCallsInBind ids b@(FunBind {}) = do
  outputTcM "Rewriting calls in bind: " b
  (b', wanteds) <- captureConstraints $ everywhereM (mkM (rewriteCall ids)) b
  if isEmptyWC wanteds then return b' else rewriteEvAfterCalls wanteds b'
rewriteCallsInBind _ b = return b

rewriteEvAfterCalls :: WantedConstraints -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteEvAfterCalls wanteds b@(FunBind {fun_ext=wrapper}) = do
  outputTcM "Captured constraints: " wanteds
  (wc, ebm) <- runTcS $ solveWanteds wanteds
  outputTcM "Resulting wc: " wc
  outputTcM "Resulting ebm: " ebm
  outputTcM "solved: " $ isSolvedWC wc
  let newEvBinds = evBindMapBinds ebm
  (wrapper', changes) <- runStateT (everywhereM (mkM (addBindsToWpLet newEvBinds)) wrapper) 0
  wrapper'' <- case changes of
    0 -> return $ wrapper' <.> WpLet (EvBinds newEvBinds)
    1 -> return wrapper'
    _ -> fail "too many WpLet"
  return b{fun_ext=wrapper''}
rewriteEvAfterCalls _ _ = fail "invalid arg"

rewriteCall :: NameData -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteCall ids expr@(XExpr (WrapExpr (HsWrap w (HsVar x (L l var)))))
  | Just (newId, predTys) <- lookupDNameEnv ids (varName var) = do
    outputTcM "Found wrapped call: " expr
    res <- tcLookup (varName var)
    case res of
      AGlobal (AnId resId) -> outputTcM "lookup: " $ varType resId
      _ -> return ()
    w' <- instCallConstraints (OccurrenceOf (varName var)) predTys
    let newWrap = w' <.> w
    outputTcM "New wrapper: " () 
    printWrapper 1 newWrap
    let newExpr = XExpr (WrapExpr (HsWrap newWrap (HsVar x (L l newId))))
    outputTcM "New call: " newExpr 
    return newExpr
  | otherwise = return expr
rewriteCall _ expr = return expr

addBindsToWpLet :: Bag EvBind -> HsWrapper -> TcStateM Int HsWrapper
addBindsToWpLet _ (WpLet (TcEvBinds _)) = fail "Encountered unzonked TcEvBinds, this should not happen"
addBindsToWpLet binds (WpLet (EvBinds binds')) = do
  let newBinds = unionBags binds binds'
  modify (+1)
  return (WpLet (EvBinds newBinds))
addBindsToWpLet _ w = return w

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

