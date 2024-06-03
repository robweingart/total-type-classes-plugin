{-# LANGUAGE LambdaCase #-}

module TestPlugin.Rewriter.Utils (outputTcM, printWrapper, printBndrTys, hsWrapperTypeSubst) where

import Data.Foldable (forM_)

import GHC.Plugins hiding (substTy)
import GHC.Tc.Types (TcM)
import GHC.Tc.Types.Evidence (HsWrapper (..), EvBind(EvBind), TcEvBinds (TcEvBinds, EvBinds), EvTerm (EvExpr))
import GHC.Core.TyCo.Rep (Type(..), Scaled (Scaled))
import GHC.Core.TyCo.Subst (substTy)


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
    Anon (Scaled _ (TyConApp _ [TyVarTy var])) _ -> outputTcM "ty var in bndr app: " $ varUnique var
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

piResultTysSubst :: HasDebugCallStack => Type -> [Type] -> (Type, Subst)
piResultTysSubst ty [] = (ty, mkEmptySubst $ mkInScopeSet emptyVarSet)
piResultTysSubst ty orig_args@(arg:args)
  | FunTy { ft_res = res } <- ty
  = piResultTysSubst res args

  | ForAllTy (Bndr tv _) res <- ty
  = go (extendTCvSubst init_subst tv arg) res args

  | Just ty' <- coreView ty
  = piResultTysSubst ty' orig_args

  | otherwise
  = pprPanic "piResultTysSubst1" (ppr ty $$ ppr orig_args)
  where
    init_subst = mkEmptySubst $ mkInScopeSet (tyCoVarsOfTypes (ty:orig_args))

    go :: Subst -> Type -> [Type] -> (Type, Subst)
    go subst ty [] = (substTyUnchecked subst ty, subst)

    go subst ty all_args@(arg:args)
      | FunTy { ft_res = res } <- ty
      = go subst res args

      | ForAllTy (Bndr tv _) res <- ty
      = go (extendTCvSubst subst tv arg) res args

      | Just ty' <- coreView ty
      = go subst ty' all_args

      | not (isEmptyTCvSubst subst)  -- See Note [Care with kind instantiation]
      = go init_subst
          (substTy subst ty)
          all_args

      | otherwise
      = -- We have not run out of arguments, but the function doesn't
        -- have the right kind to apply to them; so panic.
        -- Without the explicit isEmptyVarEnv test, an ill-kinded type
        -- would give an infinite loop, which is very unhelpful
        -- c.f. #15473
        pprPanic "piResultTysSubst2" (ppr ty $$ ppr orig_args $$ ppr all_args)

-- | The PRType (ty, tas) is short for (piResultTys ty (reverse tas))
type PRType = (Type, [Type], Subst)

prTypeType :: PRType -> (Type, Subst)
prTypeType (ty, tys, subst)
  | null tys  = (ty, subst)
  | otherwise = let (ty', subst') = piResultTysSubst ty (reverse tys) in (ty', unionSubst subst subst')

liftPRType :: (Type -> Type) -> PRType -> PRType
liftPRType f pty = (f ty, [], subst) where (ty, subst) = prTypeType pty
 
liftPRType' :: (Type -> (Type, Subst)) -> PRType -> PRType
liftPRType' f pty = (ty', [], unionSubst s1 s2)
  where
    (ty, s1) = prTypeType pty
    (ty', s2) = f ty

hsWrapperTypeSubst :: HsWrapper -> Type -> (Type, Subst)
hsWrapperTypeSubst wrap ty = prTypeType $ go wrap (ty, [], empty_subst)
  where
    empty_subst = mkEmptySubst $ mkInScopeSet emptyVarSet
    go :: HsWrapper -> PRType -> PRType
    go WpHole            = id
    go (w1 `WpCompose` w2) = go w1 . go w2
    go (WpFun _ w2 (Scaled m exp_arg))  = liftPRType' $ \t ->
      let act_res = funResultTy t
          (exp_res, subst) = hsWrapperTypeSubst w2 act_res
      in (mkFunctionType m exp_arg exp_res, subst)
    go (WpCast co)     = liftPRType $ \_ -> coercionRKind co
    go (WpEvLam v)     = liftPRType $ mkInvisFunTy (idType v)
    go (WpEvApp _)    = liftPRType $ funResultTy
    go (WpTyLam tv)    = liftPRType $ mkForAllTy (Bndr tv Inferred)
    go (WpTyApp ta)    = \(ty,tas, subst) -> (ty, ta:tas, subst)
    go (WpLet _)       = id
    go (WpMultCoercion _)  = id
