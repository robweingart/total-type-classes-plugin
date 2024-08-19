{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module Check where

import Data.Kind
import TotalClassPlugin

assertCheckResult :: forall {ck} (c :: ck). CheckTotalityResult c => String -> Bool -> Bool -> Bool -> IO ()
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

class IsNat (n :: MyNat) where

instance IsNat Z where
instance IsNat n => IsNat (S n) where

class TestMultiParam (x :: MyNat) (y :: MyNat) where

instance TestMultiParam Z Z where

instance TestMultiParam Z y => TestMultiParam Z (S y) where

instance TestMultiParam x y => TestMultiParam (S x) y

class TestNonEx (n :: MyNat) where

instance TestNonEx Z where

--instance TestNonEx (S Z) where

instance TestNonEx n => TestNonEx (S (S n))

class TestNonTerm (n :: MyNat) where

instance TestNonTerm Z
instance TestNonTerm (S n) => TestNonTerm (S n)

class TestNonADT (a :: Type) (n :: MyNat) where
instance TestNonADT a Z
instance TestNonADT a n => TestNonADT a (S n)

class TestNonADTBad (a :: Type) (n :: MyNat) where
instance TestNonADTBad (Bool -> Int) Z
instance TestNonADTBad a n => TestNonADTBad a (S n)

class TestCtxtBad (a :: Type) (n :: MyNat) where
instance TestCtxtBad a Z
instance (TestCtxtBad a n, Monoid a) => TestCtxtBad a (S n)

--instance TotalClass TestNonEx where
--  totalityEvidence = checkTotality

--instance TotalClass TestNonADTBad where
--  totalityEvidence = checkTotality

--instance TotalClass TestNonTerm where
--  totalityEvidence = checkTotality

--instance TotalClass TestCtxtBad where
--  totalityEvidence = checkTotality

instance TotalClass IsNat where
  totalityEvidence = checkTotality

instance TotalClass TestMultiParam where
  totalityEvidence = checkTotality

instance TotalClass TestNonADT where
  totalityEvidence = checkTotality
 
type Effect = (Type -> Type) -> (Type -> Type)

class Append (xs :: [Effect]) (ys :: [Effect])
instance Append '[] ys
instance Append xs ys => Append (x ': xs) ys
instance TotalClass Append where
  totalityEvidence = checkTotality

class TestPair (a :: (MyNat, MyNat)) where

instance TestPair '(Z, Z) where

instance TestPair '(Z, y) => TestPair '(Z, S y) where

instance TestPair '(x, y) => TestPair '(S x, y)

instance TotalClass TestPair where
  totalityEvidence = checkTotality

--
--class TestPartial (a :: Type) (n :: MyNat)
--instance TestPartial Bool Z
--instance TestPartial Bool n => TestPartial Bool (S n)
--instance TotalClass (TestPartial Bool) where
--  totalityEvidence = checkTotality

class TestRepeatBad (x :: MyNat) (y :: MyNat)
instance TestRepeatBad x x

--type SingI :: forall {k}. k -> Constraint
--class SingI a where
--
--instance TotalClass (SingI :: MyNat -> Constraint) where
--  totalityEvidence = checkTotality

testAll :: IO ()
testAll = do
  assertCheckResult @TestMultiParam "TestMultiParam" True  True  True
  assertCheckResult @TestNonEx      "TestNonEx"      False True  True
  assertCheckResult @TestNonTerm    "TestNonTerm"    True  False True
  assertCheckResult @TestNonADT     "TestNonADT"     True  True  True
  assertCheckResult @TestNonADTBad  "TestNonADTBad"  False True  True
  assertCheckResult @TestCtxtBad    "TestCtxtBad"    True  True  False
  --assertCheckResult @TestRepeatBad  "TestRepeatBad"    False True  True
