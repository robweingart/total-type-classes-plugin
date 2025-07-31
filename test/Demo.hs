{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}

module Demo where

import TotalClassPlugin (TotalConstraint (..))

-- Concise demo of the core functionality, corresponding to the main example from the paper

data Nat = Z | S Nat

data Vec (n :: Nat) a where
  VNil :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a

vlength :: forall n a. Vec n a -> Nat
vlength (_ :: Vec n a) = toNat @n

class IsNat (n :: Nat) where
  toNat :: Nat

instance IsNat Z where
  toNat = Z

instance (IsNat n) => IsNat (S n) where
  toNat = S (toNat @n)

instance TotalConstraint (IsNat n)
