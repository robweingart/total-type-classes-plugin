{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module TotalClassPlugin ( TotalityEvidence, CheckTotality(..), CheckTotalityResult(..), assertTotality, TotalConstraint(..), mkSecretThing, mkTotalConstraint, warnInfo) where

import Data.Kind (Constraint)
import qualified Data.Kind
import GHC.TypeLits (KnownNat, KnownChar, KnownSymbol)
import Language.Haskell.TH.Syntax

class IsClassKind c where

instance IsClassKind Constraint where

instance IsClassKind c => IsClassKind (a -> c)

data TotalityEvidence c where UnsafeTotalityEvidence :: TotalityEvidence c deriving Show

assertTotality :: IsClassKind ck => TotalityEvidence (c :: ck)
assertTotality = UnsafeTotalityEvidence

type CheckTotalityResult :: forall {ck :: Data.Kind.Type}. ck -> Constraint
class CheckTotalityResult (c :: ck) where
  isExhaustive :: Bool
  isTerminating :: Bool
  isContextOk :: Bool

type CheckTotality :: forall {ck :: Data.Kind.Type}. ck -> Constraint
class CheckTotality (c :: ck) where
  checkTotality :: TotalityEvidence c

class IsClassKind ck => TotalClass (c :: ck) where
  totalityEvidence :: TotalityEvidence c

type TotalConstraint :: Constraint -> Constraint

class TotalConstraint c where
  _totalConstraintEvidence :: TotalityEvidence c

instance TotalConstraint (KnownNat n) where
  _totalConstraintEvidence = assertTotality

instance TotalConstraint (KnownChar c) where
  _totalConstraintEvidence = assertTotality

instance TotalConstraint (KnownSymbol s) where
  _totalConstraintEvidence = assertTotality

secretInternal :: String
secretInternal = "secret"

mkSecretThing :: Q [Dec]
mkSecretThing = [d| 
  secret :: String
  secret = secretInternal |]

mkTotalConstraint :: Q Type -> Q [Dec]
mkTotalConstraint qty = do
  ty <- qty
  let (tvs, theta, constraint) = case ty of
       ForallT bndrs cxt inner -> (bndrs, cxt, inner)
       inner -> ([], [], inner)
  reportWarning ("pred: " ++ show constraint)
  headTy <- [t| TotalConstraint $(return constraint) |]
  insts <- case constraint of
    AppT (ConT cls_name) arg -> reifyInstances cls_name [arg]
    _ -> return []
  reportWarning ("instances: " ++ show insts)
  return [InstanceD Nothing theta headTy []]

warnInfo :: Name -> Q [Dec]
warnInfo name = do
  info <- reify name
  reportWarning ("info: " ++ show info)
  return []
