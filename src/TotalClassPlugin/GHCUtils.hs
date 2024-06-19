-- The contents of this file are copied, with slight modification, from the source code of the 
-- Glasgow Haskell Compiler, available at https://www.haskell.org/ghc/download_ghc_9_8_2.html,
-- which is governed by the following license:
--
--   The Glasgow Haskell Compiler License
--   
--   Copyright 2002, The University Court of the University of Glasgow. 
--   All rights reserved.
--   
--   Redistribution and use in source and binary forms, with or without
--   modification, are permitted provided that the following conditions are met:
--   
--   - Redistributions of source code must retain the above copyright notice,
--   this list of conditions and the following disclaimer.
--    
--   - Redistributions in binary form must reproduce the above copyright notice,
--   this list of conditions and the following disclaimer in the documentation
--   and/or other materials provided with the distribution.
--    
--   - Neither name of the University nor the names of its contributors may be
--   used to endorse or promote products derived from this software without
--   specific prior written permission. 
--   
--   THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY COURT OF THE UNIVERSITY OF
--   GLASGOW AND THE CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
--   INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
--   FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
--   UNIVERSITY COURT OF THE UNIVERSITY OF GLASGOW OR THE CONTRIBUTORS BE LIABLE
--   FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
--   DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
--   SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
--   CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
--   LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
--   OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
--   DAMAGE.

-- The original code can be found in the following files:
-- compiler/GHC/Core/Type.hs (piResultTys)
-- compiler/GHC/Hs/Syn/Type.hs (PRType, prTypeType, liftPRType, hsWrapperType)
-- compiler/GHC/Tc/Validity.hs (splitInstTyForValidity, checkInstTermination)

module TotalClassPlugin.GHCUtils (piResultTysSubst, hsWrapperTypeSubst, splitInstTyForValidity, checkInstTermination) where

import GHC.Plugins
import GHC.Core.TyCo.Rep (Type(..))
import GHC.Tc.Types.Evidence (HsWrapper(..))
import GHC.Core.Multiplicity (Scaled(..))
import GHC.Tc.Utils.TcType (substTy, TcPredType, pSizeTypeX, pSizeClassPredX, ltPatersonSize, PatersonCondFailureContext (..), pSizeType)
import GHC.Tc.Utils.Monad (TcM, failWithTc)
import GHC.Core.Predicate (Pred(..), classifyPredType, isCTupleClass)
import GHC.Tc.Errors.Types (TcRnMessage(..))

-- Identical to GHC.Core.Type.piResultTys, except it also returns the computed substitution
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
    go subst ty' [] = (substTyUnchecked subst ty', subst)

    go subst ty' all_args@(arg':args')
      | FunTy { ft_res = res } <- ty'
      = go subst res args'

      | ForAllTy (Bndr tv _) res <- ty'
      = go (extendTCvSubst subst tv arg') res args'

      | Just ty'' <- coreView ty'
      = go subst ty'' all_args

      | not (isEmptyTCvSubst subst)
      = go init_subst
          (substTy subst ty')
          all_args

      | otherwise
      = pprPanic "piResultTysSubst2" (ppr ty' $$ ppr orig_args $$ ppr all_args)

-- Helpers for hsWrapperTypeSubst
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

-- The same algorithm as GHC.Hs.Syn.Type.hsWrapperType, except it combines and returns the computed substitutions
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
    go (WpTyApp ta)    = \(ty',tas, subst) -> (ty', ta:tas, subst)
    go (WpLet _)       = id
    go (WpMultCoercion _)  = id

-- Exactly the same as splitInstTyForValidity in GHC.Tc.Validity, which is not exported from that module
splitInstTyForValidity :: Type -> (ThetaType, Type)
splitInstTyForValidity = split_context [] . drop_foralls
  where
    drop_foralls :: Type -> Type
    drop_foralls (ForAllTy (Bndr _tv argf) ty)
      | isInvisibleForAllTyFlag argf = drop_foralls ty
    drop_foralls ty = ty

    split_context :: ThetaType -> Type -> (ThetaType, Type)
    split_context preds (FunTy { ft_af = af, ft_arg = pred', ft_res = tau })
      | isInvisibleFunArg af = split_context (pred':preds) tau
    split_context preds ty = (reverse preds, ty)

-- Exactly the same as checkInstTermination in GHC.Tc.Validity, which is not exported from that module
checkInstTermination :: ThetaType -> TcPredType -> TcM ()
checkInstTermination theta head_pred
  = check_preds emptyVarSet theta
  where
   head_size = pSizeType head_pred
   check_preds :: VarSet -> [PredType] -> TcM ()
   check_preds foralld_tvs preds = mapM_ (check' foralld_tvs) preds

   check' :: VarSet -> PredType -> TcM ()
   check' foralld_tvs pred'
     = case classifyPredType pred' of
         EqPred {}      -> return ()
         IrredPred {}   -> check2 (pSizeTypeX foralld_tvs pred')

         ClassPred cls tys
           | isCTupleClass cls
           -> check_preds foralld_tvs tys

           | otherwise
           -> check2 (pSizeClassPredX foralld_tvs cls tys)

         ForAllPred tvs _ head_pred'
           -> check' (foralld_tvs `extendVarSetList` tvs) head_pred'
      where
        check2 pred_size
          = case pred_size `ltPatersonSize` head_size of
              Just pc_failure -> failWithTc $ TcRnPatersonCondFailure pc_failure InInstanceDecl pred' head_pred
              Nothing         -> return ()
