{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DefaultSignatures #-}

module TotalClassPlugin (TotalityEvidence, CheckTotality (..), CheckTotalityResult (..), assertTotality, TotalConstraint (..)) where

import Data.Kind (Constraint, Type)
import GHC.TypeLits (KnownChar, KnownNat, KnownSymbol)

type TotalityEvidence :: Constraint -> Type
data TotalityEvidence c where UnsafeTotalityEvidence :: TotalityEvidence c deriving (Show)

assertTotality :: TotalityEvidence c
assertTotality = UnsafeTotalityEvidence

type CheckTotalityResult :: Constraint -> Constraint
class CheckTotalityResult c where
  isExhaustive :: Bool
  isTerminating :: Bool
  isContextOk :: Bool

type CheckTotality :: Constraint -> Constraint
class CheckTotality c where
  checkTotality :: TotalityEvidence c

type TotalConstraint :: Constraint -> Constraint
class TotalConstraint c where
  _totalConstraintEvidence :: TotalityEvidence c
  default _totalConstraintEvidence :: CheckTotality c => TotalityEvidence c
  _totalConstraintEvidence = checkTotality

instance TotalConstraint (KnownNat n) where
  _totalConstraintEvidence = assertTotality

instance TotalConstraint (KnownChar c) where
  _totalConstraintEvidence = assertTotality

instance TotalConstraint (KnownSymbol s) where
  _totalConstraintEvidence = assertTotality
