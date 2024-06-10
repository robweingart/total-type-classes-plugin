{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module TestPlugin.Rewriter.Bind (rewriteBinds) where

import Data.Foldable (forM_, Foldable (toList))

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM, TcGblEnv (..), TcRef, TcLclEnv)
import GHC.Tc.Types.Evidence (HsWrapper (..), (<.>), EvBind (EvBind, eb_lhs, eb_rhs), TcEvBinds (TcEvBinds, EvBinds), isIdHsWrapper)
import GHC (GhcTc, HsBindLR (..), AbsBinds (..), ABExport (abe_mono, abe_poly, ABE, abe_wrap), TyThing (AnId), MatchGroupTc (MatchGroupTc), MatchGroup (mg_ext, MG), LHsBind, HsBind, LHsBinds, LHsLocalBinds, GhcPass (GhcTc), HsLocalBinds, HsLocalBindsLR (HsIPBinds), IPBind (IPBind), HsIPBinds (IPBinds), LIPBind)
import Data.Generics (everywhereM, mkM)
import Control.Monad.State (modify, State, runState, MonadState (put, get))
import GHC.Data.Bag (filterBagM)
import TestPlugin.Placeholder (isPlaceholder)
import GHC.Tc.Utils.TcType (mkTyCoVarTys, substTy, mkPhiTy, evVarPred)
import Data.Maybe (mapMaybe, listToMaybe)
import GHC.Tc.Utils.Monad (newTcRef, readTcRef, updTcRef, wrapLocMA, updGblEnv, getGblEnv)
import GHC.Tc.Utils.Env (tcExtendGlobalEnvImplicit)
import GHC.Types.Unique.DFM (plusUDFM)
import GHC.Core.TyCo.Rep (Type (..))

import TestPlugin.Rewriter.Env
import TestPlugin.Rewriter.Utils
import GHC.Core.Unify (matchBindFun, tcUnifyTys)
import GHC.Hs.Syn.Type (hsWrapperType)
import Control.Monad (unless, when)
import Data.Traversable (mapAccumM)

rewriteBinds :: LHsBinds GhcTc -> (UpdateEnv -> LHsBinds GhcTc -> TcM (TcGblEnv, TcLclEnv)) -> TcM (TcGblEnv, TcLclEnv)
rewriteBinds binds cont = do
  --outputFullTcM "Full before rewriteBinds: " binds
  printLnTcM "rewriteBinds {"
  updateEnv <- newTcRef emptyDNameEnv
  binds' <- everywhereM (mkM (rewriteLHsBind updateEnv)) binds
  --printLnTcM "Starting second pass"
  --binds'' <- everywhereM (mkM (rewriteFunBind updateEnv)) binds'
  printLnTcM "Finished rewriteBinds pass, checking for remaining placeholders"
  _ <- everywhereM (mkM checkDoneLHsBind) binds'
  _ <- everywhereM (mkM checkDoneHsLocalBinds) binds'
  _ <- everywhereM (mkM (checkDoneHsWrapper "Unknown wrapper:")) binds'
  _ <- everywhereM (mkM (checkDoneTcEvBinds "Unknown TcEvBinds:")) binds'
  top_ev_binds <- tcg_ev_binds <$> getGblEnv
  when (any (isPlaceholder . eb_rhs) top_ev_binds) $ failTcM $ text "Found placeholder in top-level ev binds: " <+> ppr top_ev_binds
  updates <- readTcRef updateEnv
  updGblEnv (\gbl -> gbl{tcg_binds=binds'}) $ tcExtendGlobalEnvImplicit (map (AnId . new_id) $ toList updates) $ do
    printLnTcM "}"
    cont updates binds'

rewriteLHsBind :: TcRef UpdateEnv -> LHsBind GhcTc -> TcM (LHsBind GhcTc)
rewriteLHsBind ref = wrapLocMA (rewriteXHsBindsLR ref)

rewriteXHsBindsLR :: TcRef UpdateEnv -> HsBind GhcTc -> TcM (HsBind GhcTc)
rewriteXHsBindsLR updateEnv (XHsBindsLR (AbsBinds { abs_tvs=tvs
                                                  , abs_ev_vars=ev_vars
                                                  , abs_exports=exports
                                                  , abs_ev_binds=ev_binds
                                                  , abs_binds=inner_binds
                                                  , abs_sig=sig })) = do --printLnTcM "rewriteXHsBindsLR {"
  newUpdateEnv <- newTcRef emptyDNameEnv
  --printLnTcM "Before:"
  --outputTcM "abs_tvs:" tvs
  --outputTcM "abs_ev_vars:" ev_vars
  --outputTcM "abs_ev_binds:" ev_binds
  --printLnTcM "Exports of this AbsBinds:"
  --forM_ exports $ \ABE{abe_mono=mono, abe_poly=poly, abe_wrap=wrap} -> do
  --  outputTcM "Mono id:" mono
  --  outputTcM "Mono type:" $ idType mono
  --  outputTcM "Poly id:" poly
  --  outputTcM "Poly type:" $ idType poly
  --  printLnTcM "Wrapper:"
  --  printWrapper 1 wrap
  inner_binds' <- mapM (wrapLocMA (rewriteFunBind newUpdateEnv)) inner_binds
  (added_ev_vars, ev_binds') <- mapAccumM rewrite_ev_binds [] ev_binds
  exports' <- mapM (rewriteABExport newUpdateEnv tvs ev_vars added_ev_vars) exports
  let ev_vars' = ev_vars ++ added_ev_vars
  newUpdates <- readTcRef newUpdateEnv
  updTcRef updateEnv (plusUDFM newUpdates)
  --printLnTcM "}"
  --printLnTcM "After:"
  --outputTcM "abs_ev_vars:" ev_vars'
  --outputTcM "abs_ev_binds:" ev_binds'
  --printLnTcM "Exports of this AbsBinds:"
  --forM_ exports' $ \ABE{abe_mono=mono, abe_poly=poly, abe_wrap=wrap} -> do
  --  outputTcM "Mono id:" mono
  --  outputTcM "Mono type:" $ idType mono
  --  outputTcM "Poly id:" poly
  --  outputTcM "Poly type:" $ idType poly
  --  printLnTcM "Wrapper:"
  --  printWrapper 1 wrap
  return $ XHsBindsLR (AbsBinds { abs_tvs=tvs
                                , abs_ev_vars=ev_vars'
                                , abs_exports=exports'
                                , abs_ev_binds=ev_binds'
                                , abs_binds=inner_binds'
                                , abs_sig=sig })
  where
    rewrite_ev_binds vars ebs = do
      (ev_vars', ev_binds') <- rewriteTcEvBinds ebs
      unless (null ev_vars') $ do
        outputTcM "Encountered placeholder in abs_ev_binds:" ev_binds
        outputTcM "Rewrite result:" ev_binds'
        outputTcM "Introduced ev vars:" ev_vars'
      return (vars ++ ev_vars', ev_binds')

    mono_to_poly ev_vars' ty = do
      let binders = mkTyVarBinders InferredSpec tvs
      outputTcM "Adding foralls:" binders
      let theta = map evVarPred ev_vars'
      outputTcM "Adding theta:" theta
      return $ mkInvisForAllTys binders (mkPhiTy theta ty)
  
rewriteXHsBindsLR _ b = return b

rewriteABExport :: TcRef UpdateEnv -> [TyVar] -> [EvVar] -> [EvVar] -> ABExport -> TcM ABExport
rewriteABExport updateEnv tvs old_ev_vars added_ev_vars e@ABE{abe_mono=mono, abe_poly=poly, abe_wrap=wrap} = do
  (new_mono, update_from_mono) <- do_mono_update
  let binders = mkTyVarBinders InferredSpec tvs
  outputTcM "Adding foralls:" binders
  let theta = map evVarPred (old_ev_vars ++ added_ev_vars)
  outputTcM "Adding theta:" theta
  let new_poly = setVarType poly $
                 mkInvisForAllTys binders $
                 mkPhiTy theta $
                 idType new_mono
  update_from_abs <- if
    | null added_ev_vars -> return Nothing 
    | Just last_tv <- listToMaybe (reverse tvs) -> return $ Just (map evVarPred added_ev_vars, last_tv)
    | otherwise -> failTcM $ text "Encountered placeholder in abs_ev_binds, but there are no abs_tvs"
  case (update_from_mono, update_from_abs) of
    (Nothing, Nothing) -> return ()
    (Just (theta_for_update, last_tv), Nothing) -> do_poly_update new_poly theta_for_update last_tv
    (Nothing, Just (theta_for_update, last_tv)) -> do_poly_update new_poly theta_for_update last_tv
    (Just _, Just _) -> failTcM $ text "Both inner binds and abs_ev_binds were updated"
  return e{abe_mono=new_mono,abe_poly=new_poly}
  where
    do_mono_update :: TcM (Id, Maybe (ThetaType, TyVar))
    do_mono_update = do
      updates <- readTcRef updateEnv
      case lookupDNameEnv updates (varName mono) of
        Nothing -> return (mono, Nothing)
        Just u -> do
          updTcRef updateEnv (\env -> delFromDNameEnv env (varName mono))
          return (new_id u, Just (new_theta u, last_ty_var u))
    do_poly_update new_poly theta_for_update last_tv = do
      unless (isIdHsWrapper wrap) $ failTcM $ text "Rewrite inside AbsBinds with non-identity abe_wrap"
      let update = UInfo { old_type=idType poly
                         , new_id=new_poly
                         , new_theta=theta_for_update
                         , last_ty_var=last_tv }
      updTcRef updateEnv (\env -> extendDNameEnv env (varName new_poly) update)
      
                 
        

rewriteFunBind :: TcRef UpdateEnv -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
rewriteFunBind updateEnv b@(FunBind {fun_id=(L loc fid), fun_ext=(wrapper, ctick), fun_matches=MG{mg_ext=(MatchGroupTc args res _)} }) = do
  let old_ty = varType fid
  let wrapped = hsWrapperType wrapper $ mkScaledFunTys args res
  let old_vars = mapMaybe namedBinderVar $ fst $ splitInvisPiTys old_ty
  let w_vars = mapMaybe namedBinderVar $ fst $ splitInvisPiTys wrapped
  let maybe_subst = tcUnifyTys (matchBindFun (mkVarSet w_vars)) (mkTyCoVarTys w_vars) (mkTyCoVarTys old_vars)
  wrapper_res <- rewriteHsWrapper wrapper
  case (wrapper_res, maybe_subst) of
    (Nothing, _) -> return b
    (_, Nothing) -> failTcM $ text "Failed to unify fun type"
    (Just (wrapper', theta, last_tv), Just subst) -> do
      dFlags <- getDynFlags
      printLnTcM $ "rewriteFunBind " ++ (showSDoc dFlags $ ppr fid) ++ " {"
      printLnTcM "old wrapper: "
      printWrapper 1 wrapper
      printLnTcM "new wrapper: "
      printWrapper 1 wrapper'
      let theta' = substTheta subst theta
      last_tv' <- case substTyVar subst last_tv of
        TyVarTy tv -> return tv
        _ -> failTcM $ text "substitution assigned last tv to something other than a tv"
      let rewrapped = substTy subst $ hsWrapperType wrapper' $ mkScaledFunTys args res
      new_ty <- copy_flags old_ty rewrapped
      let fid' = setVarType fid new_ty
      let uinfo = UInfo{new_id=fid',old_type=old_ty,new_theta=theta',last_ty_var=last_tv'}
      --outputTcM "Modified id: " fid'
      --outputTcM "Old type: " oldTy
      --printBndrTys oldTy
      outputTcM "New type: " $ varType fid'
      printBndrTys $ varType fid'
      outputTcM "New theta: " theta'
      forM_ theta' $ \case
        TyConApp _ [TyVarTy var] -> outputTcM "  type var in theta: " $ varUnique var
        _ -> return ()
      updTcRef updateEnv (\env -> extendDNameEnv env (varName fid') uinfo)
      printLnTcM "}"
      return b {fun_id=L loc fid', fun_ext=(wrapper', ctick)}
  where
    add_flag :: ForAllTyFlag -> State [ForAllTyFlag] ForAllTyFlag
    add_flag flag = modify (flag :) >> return flag

    get_flags :: Type -> [ForAllTyFlag]
    get_flags ty = snd $ everywhereM (mkM add_flag) ty `runState` []

    set_flag :: ForAllTyFlag -> State [ForAllTyFlag] ForAllTyFlag
    set_flag _ = do
      fs <- get
      case fs of
        [] -> error "impossible"
        (f : fs') -> do
          put fs'
          return f

    copy_flags :: Type -> Type -> TcM Type
    copy_flags src tgt = do
      let old_flags = get_flags src
      outputTcM "old flags" old_flags
      let new_flags = get_flags tgt
      outputTcM "new flags" new_flags
      unless (length old_flags == length new_flags) $ failTcM $ text "number of foralls changed, bug"
      let (result, remaining_flags) = everywhereM (mkM set_flag) tgt `runState` reverse old_flags
      unless (null remaining_flags) $ error "impossible"
      let set_flags = get_flags result
      outputTcM "set flags" set_flags
      unless (old_flags == set_flags) $ failTcM $ text "flag setting failed"
      return result
rewriteFunBind _ b = return b

namedBinderVar :: PiTyBinder -> Maybe TyCoVar
namedBinderVar (Named (Bndr var _)) = Just var
namedBinderVar _ = Nothing

rewriteHsWrapper :: HsWrapper -> TcM (Maybe (HsWrapper, [PredType], TyVar))
rewriteHsWrapper wrapper = do
  --printLnTcM "rewriteHsWrapper {"
  newArgsRef <- newTcRef []
  wrapper' <- everywhereM (mkM (rewriteWpLet newArgsRef)) wrapper
  tys <- readTcRef newArgsRef
  res <- case tys of
    [] -> return Nothing
    [[]] -> return Nothing
    [newArgTys] -> do
      tv <- lastTyVar wrapper
      return $ Just (wrapper', newArgTys, tv) 
    _ -> failTcM $ text "encountered multiple zonked WpLet, this should not happen"
  --printLnTcM "}"
  return res

rewriteWpLet :: TcRef [[PredType]] -> HsWrapper -> TcM HsWrapper
rewriteWpLet newArgsRef (WpLet ev_binds) = do
  --printLnTcM "rewriteWpLet {"
  (ev_vars, ev_binds') <- rewriteTcEvBinds ev_binds
  updTcRef newArgsRef ((varType <$> ev_vars) :)
  --printLnTcM "}"
  return $ foldr ((<.>) . WpEvLam) (WpLet ev_binds') ev_vars
rewriteWpLet _ w = return w

rewriteTcEvBinds :: TcEvBinds -> TcM ([EvVar], TcEvBinds)
rewriteTcEvBinds ebs@(TcEvBinds _) = failTcM $ text "Encountered unzonked TcEvBinds, this should not happen" <+> ppr ebs
rewriteTcEvBinds (EvBinds binds) = let (binds', ev_vars) = runState (filterBagM isNotPlaceholder binds) [] in return (ev_vars, EvBinds binds')

isNotPlaceholder :: EvBind -> State [EvVar] Bool
isNotPlaceholder (EvBind {eb_lhs=evVar, eb_rhs=evTerm})
  | isPlaceholder evTerm = do
    modify (evVar :)
    return False
  | otherwise = return True

lastTyVar :: HsWrapper -> TcM TyVar
lastTyVar w = go w >>= \case
  Nothing -> failTcM (text "Wrapper has no WpTyLam" <+> ppr w)
  Just tv -> return tv
  where
    go WpHole = return Nothing
    go (WpCompose w1 w2) = go w2 >>= \case
      Nothing -> go w1
      Just tv -> return $ Just tv
    go (WpTyLam tv) = return $ Just tv
    go (WpFun _ _ _) = failTcM (text "unexpected WpFun inside " <+> ppr w)
    go _ = return Nothing

checkDoneLHsBind :: LHsBind GhcTc -> TcM (LHsBind GhcTc)
checkDoneLHsBind = wrapLocMA checkDoneHsBind

checkDoneHsBind :: HsBind GhcTc -> TcM (HsBind GhcTc)
checkDoneHsBind xb@(XHsBindsLR (AbsBinds{abs_ev_binds=ev_binds})) = forM_ ev_binds (checkDoneTcEvBinds "AbsBinds:") >> return xb
checkDoneHsBind fb@(FunBind {fun_ext=(wrap, _)}) = checkDoneHsWrapper "FunBind wrapper:" wrap >> return fb
checkDoneHsBind b = return b

checkDoneHsWrapper :: String -> HsWrapper -> TcM HsWrapper
checkDoneHsWrapper str (WpLet ev_binds) = WpLet <$> checkDoneTcEvBinds str ev_binds
checkDoneHsWrapper _ w = return w

checkDoneHsLocalBinds :: HsLocalBinds GhcTc -> TcM (HsLocalBinds GhcTc)
checkDoneHsLocalBinds lbs@(HsIPBinds _ (IPBinds ev_binds _)) = checkDoneTcEvBinds "HsIPBinds" ev_binds >> return lbs
checkDoneHsLocalBinds lbs = return lbs

checkDoneTcEvBinds :: String -> TcEvBinds -> TcM TcEvBinds
checkDoneTcEvBinds str (EvBinds binds)
  | any (isPlaceholder . eb_rhs) binds = failTcM $ text str <+> text "Found placeholder after rewrites: " <+> ppr binds
checkDoneTcEvBinds str (TcEvBinds _) = failTcM $ text str <+> text "Encountered unzonked TcEvBinds, this should not happen"
checkDoneTcEvBinds _ ev_binds = return ev_binds
