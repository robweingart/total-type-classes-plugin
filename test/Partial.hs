{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}

module Partial where

import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import TotalClassPlugin

data MyNat = Z | S MyNat

class ListOfLength (a :: Type) (n :: MyNat) where
  mkList :: [a]

instance ListOfLength Int n where
  mkList = undefined

instance ListOfLength Bool Z where
  mkList = []

instance (ListOfLength Bool n) => ListOfLength Bool (S n) where
  mkList = False : mkList @Bool @n

class SingI (a :: k)

instance SingI (a :: Bool)

instance SingI (a :: MyNat)

instance TotalConstraint (ListOfLength Bool n)

instance TotalConstraint (SingI (a :: Bool))

foo :: forall (n :: MyNat). (ListOfLength Bool n) => Proxy n -> [Bool]
foo (_ :: Proxy n) = mkList @Bool @n

foo2 :: [Bool]
foo2 = foo (Proxy :: Proxy (S (S Z)))
