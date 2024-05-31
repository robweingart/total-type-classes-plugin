{-# OPTIONS_GHC -fplugin=TestPlugin.Plugin #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module TestModule ( f, showF, Vec(..), vlength ) where

import Data.Proxy
import TestPlugin

class MyTotalClass (a :: Bool) where
  isTrue :: Proxy a -> Bool

instance MyTotalClass True where
  isTrue _ = True

instance MyTotalClass False where
  isTrue _ = False

instance TotalClass MyTotalClass where
  totalityEvidence = assertTotality
--
f :: forall (a :: Bool). Proxy a -> Bool
f x = isTrue x

showF :: forall (a :: Bool). Proxy a -> String
showF = undefined


data MyNat = Z | S MyNat deriving Show

class IsNat (n :: MyNat) where
  natTerm :: MyNat

instance IsNat Z where
  natTerm = Z

instance IsNat n => IsNat (S n) where
  natTerm = S (natTerm @n)

instance TotalClass IsNat where
  totalityEvidence = assertTotality

data Vec (n :: MyNat) a where
  VNil :: Vec Z a
  VCons :: a -> Vec n a -> Vec (S n) a

vlength :: Vec n a -> MyNat
vlength (_ :: Vec n a) = natTerm @n
