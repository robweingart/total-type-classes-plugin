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
{-# LANGUAGE PolyKinds #-}
module Partial where
import Data.Kind (Type, Constraint)
import Data.Proxy (Proxy (..))
import TotalClassPlugin


data MyNat = Z | S MyNat

class ListOfLength (a :: Type) (n :: MyNat) where
  mkList :: [a]

instance ListOfLength Int n where
  mkList = undefined

instance ListOfLength Bool Z where
  mkList = []

instance ListOfLength Bool n => ListOfLength Bool (S n) where
  mkList = False : mkList @Bool @n

--mkTotalConstraint [t| forall n. ListOfLength Bool n |]
--warnInfo ''ListOfLength
--
class SingI (a :: k) where

instance SingI (a :: Bool) where
instance SingI (a :: MyNat) where
--
--warnInfo ''SingI
--
--mkTotalConstraint [t| forall (a :: Bool). SingI a |]

instance TotalConstraint (ListOfLength Bool n) where
  _totalConstraintEvidence = checkTotality

instance TotalConstraint (SingI (a :: Bool)) where
  _totalConstraintEvidence = checkTotality

instance TotalConstraint (Show String) where
  _totalConstraintEvidence = checkTotality

foo :: forall (n :: MyNat). Proxy n -> [Bool]
foo (_ :: Proxy n) = mkList @Bool @n
--
--foo2 :: [Bool]
--foo2 = foo (Proxy :: Proxy (S (S n)))
