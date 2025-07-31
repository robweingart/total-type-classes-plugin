{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Checker where

import Data.Kind
import TotalClassPlugin

-- `CheckTotalityResult` lets us access the result of each checking step at runtime, so we can check
-- that non-total constraints fail the check for the right reason
assertCheckResult :: forall c. (CheckTotalityResult c) => String -> Bool -> Bool -> Bool -> IO ()
assertCheckResult str ex term ctxt = do
  putStrLn str
  case (isExhaustive @c, ex) of
    (True, False) -> do
      putStrLn "This class shouldn't be exhaustive, but is"
      fail "test failure"
    (False, True) -> do
      putStrLn "This class should be exhaustive, but isn't"
      fail "test failure"
    _ -> return ()
  case (isTerminating @c, term) of
    (True, False) -> do
      putStrLn "This class shouldn't be terminating, but is"
      fail "test failure"
    (False, True) -> do
      putStrLn "This class should be terminating, but isn't"
      fail "test failure"
    _ -> return ()
  case (isContextOk @c, ctxt) of
    (True, False) -> do
      putStrLn "This class shouldn't have valid instance contexts, but does"
      fail "test failure"
    (False, True) -> do
      putStrLn "This class should have valid instance contexts, but doesn't"
      fail "test failure"
    _ -> return ()

data MyNat = Z | S MyNat

-- A basic total class
class IsNat (n :: MyNat)

instance IsNat Z

instance (IsNat n) => IsNat (S n)

-- A total class with multiple params
class TestMultiParam (x :: MyNat) (y :: MyNat)

instance TestMultiParam Z Z

instance (TestMultiParam Z y) => TestMultiParam Z (S y)

instance (TestMultiParam x y) => TestMultiParam (S x) y

-- This class is non-exhaustive (missing `S n` case)
class TestNonEx (n :: MyNat)

instance TestNonEx Z

instance (TestNonEx n) => TestNonEx (S (S n))

-- This class has a non-terminating instance
class TestNonTerm (n :: MyNat)

instance TestNonTerm Z

instance (TestNonTerm (S n)) => TestNonTerm (S n)

-- This class has a non-algebraic parameter, but is still total because it doesn't match on it
class TestNonADT (a :: Type) (n :: MyNat)

instance TestNonADT a Z

instance (TestNonADT a n) => TestNonADT a (S n)

-- This class is non-total because it matches on a non-algebraic parameter
class TestNonADTBad (a :: Type) (n :: MyNat)

instance TestNonADTBad (Bool -> Int) Z

instance (TestNonADTBad a n) => TestNonADTBad a (S n)

-- This class is total given a `Monoid a` precondition
class ListOfMempty (a :: Type) (n :: MyNat) where
  mkList :: [a]

instance ListOfMempty a Z where
  mkList = []

instance (ListOfMempty a n, Monoid a) => ListOfMempty a (S n) where
  mkList = mempty : mkList @a @n

instance Monoid a => TotalConstraint (ListOfMempty a n)

-- `TestEscape Int n` is non-total because the `S n` instance requires a precondition not matching
-- the original constraint
class TestEscape (a :: Type) (n :: MyNat)

instance TestEscape Int Z

instance (TestEscape Bool n) => TestEscape Int (S n)

-- Uncomment these instances to see the error messages produced
-- instance TotalConstraint (TestEscape Int n)

-- instance TotalConstraint (TestNonEx n) where

-- instance TotalConstraint (TestNonADTBad a n) where

-- instance TotalConstraint (TestNonTerm n) where

instance TotalConstraint (IsNat n)

instance TotalConstraint (TestMultiParam x y)

instance TotalConstraint (TestNonADT a n)

instance TotalConstraint (TestNonADTBad (Bool -> Int) n)

type Effect = (Type -> Type) -> (Type -> Type)

-- Totality by induction over type-level lists
class Append (xs :: [k]) (ys :: [k])

instance Append '[] ys

instance (Append xs ys) => Append (x ': xs) ys

instance TotalConstraint (Append xs ys)

-- Rather than a multi-parameter instance, we can also use a type-level pair
class TestPair (a :: (MyNat, MyNat))

instance TestPair '(Z, Z)

instance (TestPair '(Z, y)) => TestPair '(Z, S y)

instance (TestPair '(x, y)) => TestPair '(S x, y)

instance TotalConstraint (TestPair a)


-- `TestPartial a n` is non-total but `TestPartial Bool n` is total
class TestPartial (a :: Type) (n :: MyNat)
instance TestPartial Bool Z
instance TestPartial Bool n => TestPartial Bool (S n)
instance TotalConstraint (TestPartial Bool n)

-- Special case: if an instance requires to params to be the same, the exhaustiveness check should fail
class TestRepeat (x :: MyNat) (y :: MyNat)

instance TestRepeat x x

-- This is the signature of the `SingI` class from `singletons`
type SingI :: forall {k}. k -> Constraint
class SingI a

-- `singletons` would auto-generate this
instance SingI (n :: MyNat)

-- 
instance TotalConstraint (SingI (n :: MyNat)) where

testAll :: IO ()
testAll = do
  assertCheckResult @(forall x y. TestMultiParam x y) "TestMultiParam" True True True
  assertCheckResult @(forall n. TestNonEx n) "TestNonEx" False True True
  assertCheckResult @(forall n. TestNonTerm n) "TestNonTerm" True False True
  assertCheckResult @(forall a n. TestNonADT a n) "TestNonADT" True True True
  assertCheckResult @(forall a n. TestNonADTBad a n) "TestNonADTBad" False True True
  assertCheckResult @(forall a n. ListOfMempty a n) "ListOfMempty" True True False
  assertCheckResult @(forall a n. (Monoid a) => ListOfMempty a n) "ListOfMempty" True True True
  assertCheckResult @(forall n. TestEscape Int n) "TestEscape" True True False
  assertCheckResult @(forall k (xs :: [k]) (ys :: [k]). Append xs ys) "Append" True True True
  assertCheckResult @(forall x. TestRepeat x x) "TestRepeatOk" True True True
  assertCheckResult @(forall x y. TestRepeat x y) "TestRepeatBad" False True True
