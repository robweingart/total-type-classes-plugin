{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Demo where

import TotalClassPlugin (TotalConstraint (..), checkTotality)

data Nat = Z | S Nat

data Vec (n :: Nat) a where
  VNil :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a

vlength :: forall n a. Vec n a -> Nat
vlength (_ :: Vec n a) = natToTerm @n
--
class IsNat (n :: Nat) where
  natToTerm :: Nat

instance IsNat Z where
  natToTerm = Z

instance IsNat n => IsNat (S n) where
  natToTerm = S (natToTerm @n)

instance TotalConstraint (IsNat n) where
  _totalConstraintEvidence = checkTotality

--foo :: a -> String
--foo x = show x
