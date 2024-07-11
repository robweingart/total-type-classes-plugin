{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import TotalClassPlugin (TotalClass (..), checkTotality)

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

instance TotalClass IsNat where
  totalityEvidence = checkTotality
