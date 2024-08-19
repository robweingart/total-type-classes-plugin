{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module Partial where
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import TotalClassPlugin


data MyNat = Z | S MyNat

class ListOfLength (a :: Type) (n :: MyNat) where
  mkList :: [a]

instance ListOfLength Bool Z where
  mkList = []

instance ListOfLength Bool n => ListOfLength Bool (S n) where
  mkList = False : mkList @Bool @n
--
instance TotalConstraint (ListOfLength Bool n) where
  _totalConstraintEvidence = assertTotality

foo :: forall (n :: MyNat). Proxy n -> [Bool]
foo (_ :: Proxy n) = mkList @Bool @n
--
--foo2 :: [Bool]
--foo2 = foo (Proxy :: Proxy (S (S n)))
