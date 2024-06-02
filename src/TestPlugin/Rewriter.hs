{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter (totalTcResultAction) where

import Data.Foldable (forM_, Foldable (toList))

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcTyThing (AGlobal), TcRef)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (EvBind, eb_lhs, eb_rhs), TcEvBinds (TcEvBinds, EvBinds), EvTerm (EvExpr), EvBindMap, evBindMapBinds)
import GHC (LHsBindLR, GhcTc, HsBindLR (..), AbsBinds (..), HsExpr (..), XXExprGhcTc (..), HsWrap (..), LHsBinds, Ghc, ABExport (abe_mono, abe_poly, ABE, abe_wrap), TyThing (AnId), Docs (docs_args))
import Data.Generics (everywhereM, mkM, mkT, everywhere)
import Control.Monad.State (StateT (runStateT), MonadTrans (lift), get, modify, when, unless, put, State, runState)
import GHC.Data.Bag (filterBagM, unionBags, Bag)
import TestPlugin.Placeholder (isPlaceholder)
import GHC.Tc.Utils.TcType (mkPhiTy, TcThetaType)
import GHC.Core.TyCo.Rep (Type(TyVarTy, TyConApp, CoercionTy, CastTy, FunTy), TyCoBinder (Named, Anon), Scaled (Scaled))
import GHC.Hs.Syn.Type (hsExprType)
import Data.Maybe (mapMaybe, fromMaybe, isJust)
import GHC.Tc.Utils.Monad (captureConstraints, newTcRef, setGblEnv, getGblEnv, readTcRef, updTcRef)
import GHC.Tc.Utils.Env (tcLookup, setGlobalTypeEnv, tcExtendGlobalEnv, tcExtendGlobalEnvImplicit)
import GHC.Types.TypeEnv (extendTypeEnv, extendTypeEnvWithIds)
import GHC.Types.Unique.DFM (plusUDFM)
import GHC.Tc.Utils.Instantiate (instCallConstraints)
import GHC.Tc.Types.Origin (CtOrigin(OccurrenceOf))
import GHC.Tc.Solver (solveWanteds)
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Types.Constraint (isSolvedWC, WantedConstraints, isEmptyWC)

data UpdateInfo = UInfo { old_type :: Type, new_id :: Id, new_theta :: TcThetaType }

type UpdateEnv = DNameEnv UpdateInfo

totalTcResultAction :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
totalTcResultAction _ _ gbl = do
  forM_ (tcg_binds gbl) (printInnerBinds 0)
  --outputTcM "type env: " $ tcg_type_env gbl
  gbl' <- rewriteBinds gbl
  setGblEnv gbl' $ do
    typeEnv <- tcg_type_env <$> getGblEnv
    --outputTcM "Final type env: " $ typeEnv
    -- forM_ (nonDetNameEnvElts typeEnv) $ \case
    --   AnId resId -> do
    --     outputTcM "env var: " $ resId
    --     outputTcM "env unique: " $ varUnique resId
    --     outputTcM "env type: " $ varType resId
    --   _ -> return ()
    --forM_ allIds $ \(var, _) -> do
    --  outputTcM "lookup var: " $ var
    --  outputTcM "lookup unique: " $ varUnique var
    --  res <- tcLookup (varName var)
    --  case res of
    --    AGlobal (AnId resId) -> do
    --      outputTcM "lookup type: " $ varType resId
    --    _ -> return ()
    getGblEnv

rewriteBinds :: TcGblEnv -> TcM TcGblEnv
rewriteBinds gbl = do
  let binds = tcg_binds gbl
  updateEnv <- newTcRef emptyDNameEnv
  binds' <- everywhereM (mkM (rewriteHsBindLR updateEnv)) binds
  updates <- readTcRef updateEnv
  forM_ updates $ \UInfo{new_id=id', old_type=oldTy, new_theta=newTheta} -> do
   outputTcM "Modified id: " id'
   outputTcM "New type: " $ varType id'
   printBndrTys $ varType id'
   outputTcM "Old type: " oldTy
   printBndrTys oldTy
   outputTcM "New theta: " newTheta
   return ()
  setGblEnv gbl{tcg_binds = binds'} $ tcExtendGlobalEnvImplicit ((\UInfo{new_id=id'} -> AnId id') <$> toList updates) $ do
    gbl' <- getGblEnv
    rewriteCalls updates gbl'


rewriteCalls :: UpdateEnv -> TcGblEnv -> TcM TcGblEnv
rewriteCalls ids gbl
  | isEmptyDNameEnv ids = return gbl
  | otherwise = do
    binds' <- everywhereM (mkM (rewriteCallsInBind ids)) (tcg_binds gbl)
    setGblEnv gbl{tcg_binds = binds'} $ do
      gbl' <- getGblEnv
      rewriteBinds gbl'

rewriteHsBindLR :: TcRef UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteHsBindLR updateEnv (XHsBindsLR ab@(AbsBinds {abs_exports=exports, abs_binds=inner_binds})) = do
  newUpdateEnv <- newTcRef emptyDNameEnv
  inner_binds' <- everywhereM (mkM (rewriteInnerHsBindLR newUpdateEnv)) inner_binds
  exports' <- mapM (rewriteABExport newUpdateEnv) exports
  newUpdates <- readTcRef newUpdateEnv
  --lift $ outputTcM "newly added: " newIds
  updTcRef updateEnv (plusUDFM newUpdates)
  return $ XHsBindsLR ab{abs_binds=inner_binds',abs_exports=exports'}
rewriteHsBindLR _ b = return b

--rewriteABExport :: ABExport -> TcStateM UpdateEnv ABExport
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

rewriteABExport :: TcRef UpdateEnv -> ABExport -> TcM ABExport
rewriteABExport updateEnv e@ABE{abe_mono=mono, abe_poly=poly, abe_wrap=wrap} = do
  updates <- readTcRef updateEnv
  if isEmptyDNameEnv updates then return e else do
    case lookupDNameEnv updates (varName mono) of
      Nothing -> return e
      Just u -> do
        let newMono = new_id u
        let newPoly = setVarType poly (varType newMono)
        --lift $ outputTcM "new_mono: " $ varType newMono
        updTcRef updateEnv (\env -> delFromDNameEnv env (varName mono))
        updTcRef updateEnv (\env -> extendDNameEnv env (varName poly) u{new_id=newPoly})
        --lift $ outputTcM "new_poly: " $ varType newPoly
        --lift $ outputTcM "new_poly invispitys: " $ splitInvisPiTys $ varType newPoly
        --modified' <- get
        --lift $ outputTcM "new_poly (actual): " $ fst <$> lookupDNameEnv modified' (varName poly)
        return e{abe_mono=newMono,abe_poly=newPoly}

rewriteInnerHsBindLR :: TcRef UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteInnerHsBindLR updateEnv b@(FunBind {fun_id=(L loc fid), fun_ext=wrapper }) = do
  result <- rewriteHsWrapper wrapper
  case result of
    Nothing -> return b
    Just (wrapper', newArgTys) -> do
      let oldTy = varType fid
      newTy <- updateFunType oldTy (wrapperBinders wrapper) newArgTys
      outputTcM "new ty: " newTy
      case splitInvisPiTys newTy of
        ([Named (Bndr var _), Anon _ (Scaled _ (TyConApp _ [TyVarTy var']))], _) -> do
          outputTcM "var in ty binder: " $ varUnique var
          outputTcM "var in inst binder: " $ varUnique var'
        _ -> return ()
      let fid' = setVarType fid newTy
      updTcRef updateEnv (\env -> extendDNameEnv env (varName fid') UInfo{new_id=fid',old_type=oldTy,new_theta=newArgTys})
      return b {fun_id=L loc fid', fun_ext=wrapper'}
rewriteInnerHsBindLR _ b = return b

wrapperBinders :: HsWrapper -> [Var]
wrapperBinders (WpCompose w1 w2) = wrapperBinders w1 ++ wrapperBinders w2
wrapperBinders (WpTyLam var) = [var]
wrapperBinders _ = []

rewriteHsWrapper :: HsWrapper -> TcM (Maybe (HsWrapper, [PredType]))
rewriteHsWrapper wrapper = do
  newArgsRef <- newTcRef []
  wrapper' <- everywhereM (mkM (rewriteWpLet newArgsRef)) wrapper
  tys <- readTcRef newArgsRef
  case tys of
    [] -> return Nothing
    [[]] -> return Nothing
    [newArgTys] -> return $ Just (wrapper', newArgTys) 
    _ -> fail "encountered multiple WpLet, this should not happen"

rewriteWpLet :: TcRef [[PredType]] -> HsWrapper -> TcM HsWrapper
rewriteWpLet _ (WpLet (TcEvBinds _)) = fail "Encountered unzonked TcEvBinds, this should not happen"
rewriteWpLet newArgsRef (WpLet (EvBinds binds)) = do
  let (binds', evVars) = runState (filterBagM isNotPlaceholder binds) []
  updTcRef newArgsRef ((varType <$> evVars) :)
  return $ foldr ((<.>) . WpEvLam) (WpLet (EvBinds binds')) evVars
rewriteWpLet _ w = return w

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

rewriteCallsInBind :: UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
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
  counter <- newTcRef 0
  wrapper' <- everywhereM (mkM (addBindsToWpLet counter newEvBinds)) wrapper
  changes <- readTcRef counter
  wrapper'' <- case changes of
    0 -> return $ wrapper' <.> WpLet (EvBinds newEvBinds)
    1 -> return wrapper'
    _ -> fail "too many WpLet"
  return b{fun_ext=wrapper''}
rewriteEvAfterCalls _ _ = fail "invalid arg"

rewriteCall :: UpdateEnv -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
rewriteCall ids expr@(XExpr (WrapExpr (HsWrap w (HsVar x (L l var)))))
  | Just UInfo{new_id=newId, new_theta=predTys} <- lookupDNameEnv ids (varName var) = do
    outputTcM "Found wrapped call: " expr
    outputTcM "wrapper: " ()
    printWrapper 1 w
    outputTcM "type: " $ hsExprType expr
    case hsExprType expr of
      FunTy _ _ (TyConApp _ [_, TyVarTy tyVar]) _ -> outputTcM "Ty var in arg: " $ varUnique tyVar
      _ -> return ()
    outputTcM "inner type: " $ varType var
    printBndrTys $ varType var
    
    w' <- instCallConstraints (OccurrenceOf (varName var)) predTys
    let newWrap = w' <.> w
    outputTcM "New wrapper: " () 
    printWrapper 1 newWrap
    let newExpr = XExpr (WrapExpr (HsWrap newWrap (HsVar x (L l newId))))
    outputTcM "New call: " newExpr 
    return newExpr
  | otherwise = return expr
rewriteCall _ expr = return expr

addBindsToWpLet :: TcRef Int -> Bag EvBind -> HsWrapper -> TcM HsWrapper
addBindsToWpLet _ _ (WpLet (TcEvBinds _)) = fail "Encountered unzonked TcEvBinds, this should not happen"
addBindsToWpLet counter binds (WpLet (EvBinds binds')) = do
  let newBinds = unionBags binds binds'
  updTcRef counter (+1)
  return (WpLet (EvBinds newBinds))
addBindsToWpLet _ _ w = return w

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

