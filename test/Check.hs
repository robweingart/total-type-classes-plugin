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
{-# LANGUAGE UndecidableInstances #-}

module Check where

import Data.Kind
import TotalClassPlugin
import Control.Exception (evaluate, assert)

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

class TestGood (x :: MyNat) (y :: MyNat) where

instance TestGood Z Z where

instance TestGood Z y => TestGood Z (S y) where

instance TestGood x y => TestGood (S x) y

class TestNonEx (n :: MyNat) where

instance TestNonEx Z where

--instance TestNonEx (S Z) where

instance TestNonEx n => TestNonEx (S (S n))

class TestNonTerm (n :: MyNat) where

instance TestNonTerm Z
instance TestNonTerm (S n) => TestNonTerm (S n)

instance TotalClass IsNat where
  totalityEvidence = checkTotality 

class TestNonADTGood (a :: Type) (n :: MyNat) where
instance TestNonADTGood a Z
instance TestNonADTGood a n => TestNonADTGood a (S n)

class TestNonADTBad (a :: Type) (n :: MyNat) where
instance TestNonADTBad (Bool -> Int) Z
instance TestNonADTBad a n => TestNonADTBad a (S n)

class TestCtxtBad (a :: Type) (n :: MyNat) where
instance TestCtxtBad a Z
instance (TestCtxtBad a n, Monoid a) => TestCtxtBad a (S n)

testAll :: IO ()
testAll = do
  assertCheckResult @TestGood       "TestGood"       True  True  True
  assertCheckResult @TestNonEx      "TestNonEx"      False True  True
  assertCheckResult @TestNonTerm    "TestNonTerm"    True  False True
  assertCheckResult @TestNonADTGood "TestNonADTGood" True  True  True
  assertCheckResult @TestNonADTBad  "TestNonADTBad"  False True  True
  assertCheckResult @TestCtxtBad    "TestCtxtBad"    True  True  False
