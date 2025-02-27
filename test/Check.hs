{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}

module Check where

import Data.Kind
import Data.Monoid
import TotalClassPlugin

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

class IsNat (n :: MyNat)

instance IsNat Z

instance (IsNat n) => IsNat (S n)

class TestMultiParam (x :: MyNat) (y :: MyNat)

instance TestMultiParam Z Z

instance (TestMultiParam Z y) => TestMultiParam Z (S y)

instance (TestMultiParam x y) => TestMultiParam (S x) y

class TestNonEx (n :: MyNat)

instance TestNonEx Z

-- instance TestNonEx (S Z) where

instance (TestNonEx n) => TestNonEx (S (S n))

-- instance TotalConstraint (TestNonEx n)

class TestNonTerm (n :: MyNat)

instance TestNonTerm Z

instance (TestNonTerm (S n)) => TestNonTerm (S n)

class TestNonADT (a :: Type) (n :: MyNat)

instance TestNonADT a Z

instance (TestNonADT a n) => TestNonADT a (S n)

class TestNonADTBad (a :: Type) (n :: MyNat)

instance TestNonADTBad (Bool -> Int) Z

instance (TestNonADTBad a n) => TestNonADTBad a (S n)

-- instance TotalConstraint (TestNonADTBad a n)

class ListOfMempty (a :: Type) (n :: MyNat) where
  mkList :: [a]

instance ListOfMempty a Z where
  mkList = []

instance (ListOfMempty a n, Monoid a) => ListOfMempty a (S n) where
  mkList = mempty : mkList @a @n

instance TotalConstraint (ListOfMempty (Sum Int) n)
-- instance Monoid a => TotalConstraint (ListOfMempty a n)

-- instance TotalConstraint (forall a n. Monoid a => ListOfMempty a n)

class TestEscape (a :: Type) (n :: MyNat)

-- instance TestEscape Bool n
instance TestEscape Int Z

instance (TestEscape Bool n) => TestEscape Int (S n)

-- instance TotalConstraint (TestEscape Int n)

-- instance TotalConstraint (TestNonEx n) where
--  _totalConstraintEvidence = checkTotality

-- instance TotalConstraint (TestNonADTBad a n) where
--  _totalConstraintEvidence = checkTotality

-- instance TotalConstraint (TestNonTerm n) where
--  _totalConstraintEvidence = checkTotality

-- instance TotalConstraint (TestCtxtBad a n) where
--  _totalConstraintEvidence = checkTotality

instance TotalConstraint (IsNat n) where

instance TotalConstraint (TestMultiParam x y)

instance TotalConstraint (TestNonADT a n)

type Effect = (Type -> Type) -> (Type -> Type)

class Append (xs :: [k]) (ys :: [k])

instance Append '[] ys

instance (Append xs ys) => Append (x ': xs) ys

instance TotalConstraint (Append xs ys)

class TestPair (a :: (MyNat, MyNat))

instance TestPair '(Z, Z)

instance (TestPair '(Z, y)) => TestPair '(Z, S y)

instance (TestPair '(x, y)) => TestPair '(S x, y)

instance TotalConstraint (TestPair a)

--
-- class TestPartial (a :: Type) (n :: MyNat)
-- instance TestPartial Bool Z
-- instance TestPartial Bool n => TestPartial Bool (S n)
-- instance TotalConstraint (TestPartial Bool n) where
--  _totalConstraintEvidence = checkTotality

class TestRepeat (x :: MyNat) (y :: MyNat)

instance TestRepeat x x

-- type SingI :: forall {k}. k -> Constraint
-- class SingI a where
--
-- instance TotalConstraint (SingI (n :: MyNat)) where
--  _totalConstraintEvidence = checkTotality

testAll :: IO ()
testAll = do
  assertCheckResult @(forall x y. TestMultiParam x y) "TestMultiParam" True True True
  assertCheckResult @(forall n. TestNonEx n) "TestNonEx" False True True
  assertCheckResult @(forall n. TestNonTerm n) "TestNonTerm" True False True
  assertCheckResult @(forall a n. TestNonADT a n) "TestNonADT" True True True
  assertCheckResult @(forall a n. TestNonADTBad a n) "TestNonADTBad" False True True
  assertCheckResult @(forall a n. ListOfMempty a n) "ListOfMempty" True True False
  assertCheckResult @(forall a n. Monoid a => ListOfMempty a n) "ListOfMempty" True True True
  assertCheckResult @(forall n. TestEscape Int n) "TestEscape" True True False
  assertCheckResult @(forall k (xs :: [k]) (ys :: [k]). Append xs ys) "Append" True True True
  assertCheckResult @(forall x. TestRepeat x x) "TestRepeatOk" True True True
  assertCheckResult @(forall x y. TestRepeat x y) "TestRepeatBad" False True True
