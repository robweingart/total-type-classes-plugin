{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}
{-# OPTIONS_GHC -Wno-unused-pattern-binds #-}

module Rewriter where

import Data.Proxy
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import TotalClassPlugin (TotalConstraint (..), CheckTotality (checkTotality))
import Data.Monoid (Sum)

-- This module contains various examples where the rewriter successfully adds constraints.
-- Try running `cabal repl` and using the `:t` command to see the final types

testBaseline :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testBaseline x = symbolVal x

-- Function requiring rewrite
testSimple :: forall (s :: Symbol). Proxy s -> String
testSimple x = symbolVal x

-- Function requiring rewrite
testExposedSimple :: forall (s :: Symbol). Proxy s -> String
testExposedSimple x = symbolVal x

-- Call to rewritten function, caller already has constraint
testExposedCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testExposedCall1 x = testSimple x

-- Call to rewritten function, caller will also need rewrite
testExposedCall2 :: forall (s :: Symbol). Proxy s -> String
testExposedCall2 x = testSimple x

-- Call to rewritten function, caller already has constraint
testCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testCall1 x = testSimple x

-- Call to rewritten function, caller will also need rewrite
testCall2 :: forall (s :: Symbol). Proxy s -> String
testCall2 x = testSimple x

-- Multiple uses of the same missing constraint
testSimples1 :: forall (s :: Symbol). Proxy s -> String
testSimples1 x = symbolVal x ++ " " ++ symbolVal x

-- Multiple uses of the same provided constraint
testSimples2 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testSimples2 x = symbolVal x ++ " " ++ symbolVal x

-- Two different provided constraints
testSimples3 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testSimples3 x y = symbolVal x ++ " " ++ symbolVal y

-- Two different missing constraints
testSimples4 :: forall (s1 :: Symbol) (s2 :: Symbol). Proxy s1 -> Proxy s2 -> String
testSimples4 x y = symbolVal x ++ " " ++ symbolVal y

-- Only the "first" constraint already provided
testSimples5 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1) => Proxy s1 -> Proxy s2 -> String
testSimples5 x y = symbolVal x ++ " " ++ symbolVal y

-- Only the "second" constraint already provided
testSimples6 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testSimples6 x y = symbolVal x ++ " " ++ symbolVal y

-- Multiple calls with same provided constraint
testCalls1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testCalls1 x = testSimple x ++ " " ++ testSimple x

-- Multiple calls with the same missing constraint
testCalls2 :: forall (s :: Symbol). Proxy s -> String
testCalls2 x = testSimple x ++ " " ++ testSimple x

-- Multiple calls with different provided constraints
testCalls3 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testCalls3 x y = testSimple x ++ " " ++ testSimple y

-- Multiple calls with different missing constraints
testCalls4 :: forall (s1 :: Symbol) (s2 :: Symbol). Proxy s1 -> Proxy s2 -> String
testCalls4 x y = testSimple x ++ " " ++ testSimple y

-- Only the "first" constraint already provided
testCalls5 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1) => Proxy s1 -> Proxy s2 -> String
testCalls5 x y = testSimple x ++ " " ++ testSimple y

-- Only the "second" constraint already provided
testCalls6 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testCalls6 x y = testSimple x ++ " " ++ testSimple y

-- As above, with another layer of rewriting
testCalls'1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testCalls'1 x = testSimples1 x

testCalls'2 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testCalls'2 x = testSimples2 x

testCalls'3 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testCalls'3 x y = testSimples3 x y

testCalls'4 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testCalls'4 x y = testSimples4 x y

testCalls'5 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testCalls'5 x y = testSimples5 x y

testCalls'6 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testCalls'6 x y = testSimples6 x y

-- One constraint already provided, but in a weird place
testWeirdOrderSimples :: forall (s1 :: Symbol). (KnownSymbol s1) => forall (s2 :: Symbol). Proxy s1 -> Proxy s2 -> String
testWeirdOrderSimples x y = symbolVal x ++ " " ++ symbolVal y

-- Both constraints provided, but in a weird order
testWeirdOrderCalls1 :: forall (s1 :: Symbol). (KnownSymbol s1) => forall (s2 :: Symbol). (KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testWeirdOrderCalls1 x y = testSimple x ++ " " ++ testSimple y

-- One constraint already provided, but in a weird place
testWeirdOrderCalls2 :: forall (s1 :: Symbol). (KnownSymbol s1) => forall (s2 :: Symbol). Proxy s1 -> Proxy s2 -> String
testWeirdOrderCalls2 x y = testSimple x ++ " " ++ testSimple y

-- Calling a function with weird binder order
testWeirdOrderCalls3 :: forall (s1 :: Symbol). forall (s2 :: Symbol). Proxy s1 -> Proxy s2 -> String
testWeirdOrderCalls3 x y = testWeirdOrderCalls2 x y

-- Cast the called function to its rewritten type
testPolyCastCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testPolyCastCall1 x = (testSimple :: forall (s' :: Symbol). (KnownSymbol s') => Proxy s' -> String) x

-- Cast the called function to its rewritten type
testPolyCastCall2 :: forall (s :: Symbol). Proxy s -> String
testPolyCastCall2 x = (testSimple :: forall (s' :: Symbol). (KnownSymbol s') => Proxy s' -> String) x

-- Cast the called function to its rewritten type with a known type param
testMonoCastCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testMonoCastCall1 (x :: Proxy s) = (testSimple :: (KnownSymbol s) => Proxy s -> String) x

-- Cast the called function to its rewritten type with a known type param
testMonoCastCall2 :: forall (s :: Symbol). Proxy s -> String
testMonoCastCall2 (x :: Proxy s) = (testSimple :: (KnownSymbol s) => Proxy s -> String) x

-- Cast the called function to its old type
testPolyCastCall'1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testPolyCastCall'1 x = (testSimple :: forall (s' :: Symbol). Proxy s' -> String) x

-- Cast the called function to its old type
testPolyCastCall'2 :: forall (s :: Symbol). Proxy s -> String
testPolyCastCall'2 x = (testSimple :: forall (s' :: Symbol). Proxy s' -> String) x

-- Cast the called function to its old type with a known type param
testMonoCastCall'1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testMonoCastCall'1 (x :: Proxy s) = (testSimple :: Proxy s -> String) x

-- Cast the called function to its old type with a known type param
testMonoCastCall'2 :: forall (s :: Symbol). Proxy s -> String
testMonoCastCall'2 (x :: Proxy s) = (testSimple :: Proxy s -> String) x

-- Eta reduced calls
testEtaSimple :: forall (s :: Symbol). Proxy s -> String
testEtaSimple = symbolVal

testEtaCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testEtaCall1 = testSimple

testEtaCall2 :: forall (s :: Symbol). Proxy s -> String
testEtaCall2 = testSimple

-- Nested polymorphic function
testNestedPolySimple :: forall (s :: Symbol). Proxy s -> String
testNestedPolySimple x = goPolySimple x
  where
    goPolySimple :: forall (s' :: Symbol). Proxy s' -> String
    goPolySimple x' = symbolVal x'

testNestedMonoSimple :: forall (s :: Symbol). Proxy s -> String
testNestedMonoSimple x = goMonoSimple x
  where
    goMonoSimple :: Proxy s -> String
    goMonoSimple x' = symbolVal x'

testNestedInferredSimple :: forall (s :: Symbol). Proxy s -> String
testNestedInferredSimple x = goInferredSimple x
  where
    goInferredSimple x' = symbolVal x'

testNestedPolyCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testNestedPolyCall1 x = goPolyCall1 x
  where
    goPolyCall1 :: forall (s' :: Symbol). (KnownSymbol s') => Proxy s' -> String
    goPolyCall1 x' = testSimple x'

testNestedPolyCall2 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testNestedPolyCall2 x = goPolyCall2 x
  where
    goPolyCall2 :: forall (s' :: Symbol). Proxy s' -> String
    goPolyCall2 x' = testSimple x'

testNestedPolyCall3 :: forall (s :: Symbol). Proxy s -> String
testNestedPolyCall3 x = goPolyCall3 x
  where
    goPolyCall3 :: forall (s' :: Symbol). Proxy s' -> String
    goPolyCall3 x' = testSimple x'

testNestedMonoCall :: forall (s :: Symbol). Proxy s -> String
testNestedMonoCall x = goMonoCall x
  where
    goMonoCall :: Proxy s -> String
    goMonoCall x' = testSimple x'

testNestedInferredCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testNestedInferredCall1 x = goInferredCall1 x
  where
    goInferredCall1 x' = testSimple x'

testNestedInferredCall2 :: forall (s :: Symbol). Proxy s -> String
testNestedInferredCall2 x = goInferredCall2 x
  where
    goInferredCall2 x' = testSimple x'

-- Rewriting call wrapped in lambda
testLambdaSimple :: forall (s :: Symbol). Proxy s -> String
testLambdaSimple = \x -> symbolVal x

testLambdaCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testLambdaCall1 = \x -> testSimple x

testLambdaCall2 :: forall (s :: Symbol). Proxy s -> String
testLambdaCall2 = \x -> testSimple x

-- Rewriting at an explicit type applications
testExpAppSimple :: forall (s :: Symbol). Proxy s -> String
testExpAppSimple x = symbolVal @s x

testExpAppCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testExpAppCall1 x = testSimple @s x

testExpAppCall2 :: forall (s :: Symbol). Proxy s -> String
testExpAppCall2 x = testSimple @s x

testExpAppCalls'1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testExpAppCalls'1 x = testSimples1 @s x

testExpAppCalls'2 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testExpAppCalls'2 x = testSimples2 @s x

testExpAppCalls'3 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testExpAppCalls'3 x y = testSimples3 @s1 @s2 x y

testExpAppCalls'4 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testExpAppCalls'4 x y = testSimples4 @s1 @s2 x y

testExpAppCalls'5 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testExpAppCalls'5 x y = testSimples5 @s1 @s2 x y

testExpAppCalls'6 :: forall (s1 :: Symbol) (s2 :: Symbol). (KnownSymbol s1, KnownSymbol s2) => Proxy s1 -> Proxy s2 -> String
testExpAppCalls'6 x y = testSimples6 @s1 @s2 x y

-- More unusual binder orders
testArgBeforeTy :: () -> forall (s :: Symbol). Proxy s -> String
testArgBeforeTy () x = symbolVal x

testArgBeforeTy' :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testArgBeforeTy' x = testArgBeforeTy () x

-- Nested eta reduced functions
testNestedEtaSimple :: forall (s :: Symbol). Proxy s -> String
testNestedEtaSimple x = go x
  where
    go = symbolVal

testNestedEtaCall1 :: forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String
testNestedEtaCall1 x = go x
  where
    go = testSimple

testNestedEtaCall2 :: forall (s :: Symbol). Proxy s -> String
testNestedEtaCall2 x = go x
  where
    go = testSimple

-- The example from the paper
data MyNat = Z | S MyNat deriving (Show)

class IsNat (n :: MyNat) where
  toNat :: MyNat

instance IsNat Z where
  toNat = Z

instance (IsNat n) => IsNat (S n) where
  toNat = S (toNat @n)

infixr 5 :>

data Vec (n :: MyNat) a where
  VNil :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a

instance TotalConstraint (IsNat n)

vlength :: Vec n a -> MyNat
vlength (_ :: Vec n a) = toNat @n

--class C (x :: MyNat) (y :: MyNat) where
--  showN :: String
--
--instance C Z y where
--  showN = ""
--
--instance (C n y) => C (S n) y where
--  showN = "." ++ showN @n @y
--
--instance TotalConstraint (C x y)
--
--f :: forall (m :: MyNat) (n :: MyNat). C m n => String
--f =  showN @m @n ++ f @(S m) @(S n)
--
--g :: forall (m :: MyNat) (n :: MyNat). C m n => String
--g =  showN @m @n ++ f @(S m) @(S n)

testRankNCall :: String
testRankNCall = go testSimple
  where
    go :: (forall (s :: Symbol). (KnownSymbol s) => Proxy s -> String) -> String
    go f = f (Proxy :: Proxy "testRankNCall")

-- Instantiate a rewritten function using a type variable obtained from TypeAbstractions
testTypeAbsCall1 :: forall (s :: Symbol). KnownSymbol s => String
testTypeAbsCall1 @s' = testSimple (Proxy :: Proxy s')

-- The `Proxy` argument is only here to stop GHC from complaining about `s` being unused
-- (note such an unused forall would always be pointless without rewriting)
testTypeAbsCall2 :: forall (s :: Symbol). Proxy s -> String
testTypeAbsCall2 @s' _ = testSimple (Proxy :: Proxy s')

type PlusOne (n :: MyNat) = S n

-- GHC looks through the alias and applies available instances before calling plugins, so here
-- we will add `IsNat n`, not `IsNat (PlusOne n)` or `IsNat (S n)`
testTypeAliasCall :: forall (n :: MyNat) a. Vec (PlusOne n) a -> MyNat
testTypeAliasCall v = vlength v

type family TypeFam (n :: MyNat) a :: MyNat where
  TypeFam n Bool = n
  TypeFam n Int = Z

-- The type family will beta-reduced away before the plugin invocation, so we add `IsNat n`
testReducibleTypeFamilyCall :: forall (n :: MyNat) a. Vec (TypeFam n Bool) a -> MyNat
testReducibleTypeFamilyCall v = vlength v
  

type family MinusOne (n :: MyNat) :: MyNat where
  MinusOne Z = Z
  MinusOne (S n) = n

-- Here the type family can't be reduced without knowing `n`, so the plugin must add `IsNat (MinusOne n)`
-- The `Proxy` argument is only there to avoid an ambiguity issue
testIrreducibleTypeFamilyCall :: forall (n :: MyNat) a. Proxy n -> Vec (MinusOne n) a -> MyNat
testIrreducibleTypeFamilyCall Proxy v = vlength v

--testVis1 :: forall (s :: Symbol) -> KnownSymbol s => String
--testVis1 (type s') = testSimple (Proxy :: Proxy s')
--
--testVis2 :: forall (s :: Symbol) -> String
--testVis2 (type s) = testSimple (Proxy :: Proxy s)
--
--testVisCall1 :: forall (s :: Symbol). KnownSymbol s => Proxy s -> String
--testVisCall1 (Proxy :: Proxy s) = testVis1 (type s)
--
--testVisCall2 :: forall (s :: Symbol). Proxy s -> String
--testVisCall2 (Proxy :: Proxy s) = testVis1 (type s)



class ListOfFalse (n :: MyNat) a where
  mkListOfFalse :: [a]

instance ListOfFalse Z a where
  mkListOfFalse = []

instance ListOfFalse n Bool => ListOfFalse (S n) Bool where
  mkListOfFalse = False : mkListOfFalse @n

instance TotalConstraint (ListOfFalse n Bool) where
  _totalConstraintEvidence = checkTotality

-- Because the needed constraint matches the restricted instantiation `ListOfFalse n Bool`,
-- the total constraint declaration applies and it gets inserted
testListOfFalse :: forall (n :: MyNat). Proxy n -> [Bool]
testListOfFalse (Proxy :: Proxy n) = mkListOfFalse @n @Bool

class ListOfMempty (n :: MyNat) a where
  mkListOfMempty :: [a]

instance ListOfMempty Z a where
  mkListOfMempty = []

instance (Monoid a, ListOfMempty n a) => ListOfMempty (S n) a where
  mkListOfMempty = mempty : mkListOfMempty @n

instance Monoid a => TotalConstraint (ListOfMempty n a) where
  _totalConstraintEvidence = checkTotality

-- Because the `Monoid a` precondition is satisfied, `ListOfMempty n a` is inserted
testListOfMempty :: forall (n :: MyNat) a. Monoid a => Proxy n -> Proxy a -> [a]
testListOfMempty (Proxy :: Proxy n) (Proxy :: Proxy a) = mkListOfMempty @n @a

--type family F (n :: MyNat) :: MyNat
--
--class Cl (n :: MyNat) where
--  m :: String
--
--instance IsNat (F n) => Cl n where
--  m = ""
--
--instance TotalConstraint (Cl n)
--
--q :: String
--q = m

plus :: MyNat -> MyNat -> MyNat
plus Z y = y
plus (S x) y = S (plus x y)

vlength' :: (IsNat n) => Vec n a -> MyNat
vlength' (_ :: Vec n a) = toNat @n

data VecSomeLength a where
  VecSomeLength :: (IsNat n) => Vec n a -> VecSomeLength a

data VecList a where
  VLNil :: VecList a
  VLCons :: (IsNat n) => Vec n a -> VecList a -> VecList a

foldrVecList :: forall a b. (forall n. (IsNat n) => Vec n a -> b -> b) -> b -> VecList a -> b
foldrVecList f z = go
  where
    go VLNil = z
    go (VLCons v vs) = f v (go vs)

-- We can use a rewritten function in the argument of a higher-order function
-- (but the `IsNat` in `foldrVecList` has to be written manually)
sumLengths :: VecList a -> MyNat
sumLengths vs = foldrVecList (\v n -> vlength v `plus` n) Z vs

-- When rewriting a call, we can use a constraint coming from a GADT constructor, without any type annotation
sumLengthsInline :: [VecSomeLength a] -> MyNat
sumLengthsInline vs = foldr (\(VecSomeLength v) n -> vlength v `plus` n) Z vs

data WrappedIsNat n where WrappedIsNat :: IsNat n => WrappedIsNat n

-- We can also use a GADT-wrapped constraint obtained using a `let` binding
letExistential :: WrappedIsNat n -> Vec n a -> MyNat
letExistential x v = let WrappedIsNat = x in vlength v

examples :: Vec n String -> MyNat
examples v =        vlLocal v
             `plus` vlLambda v
             `plus` vlEtaReduced v
             `plus` vlTypeApplied v
             `plus` vlExprSig v
  where
    vlLocal v' = vlength v'
    vlLambda = \v' -> vlength v'
    vlEtaReduced = vlength
    vlTypeApplied = vlength @_ @String
    vlExprSig = vlength :: forall m. Vec m String -> MyNat

-- We run all of the functions to check they actually work at runtime
-- (in particular, the KnownSymbol in each one is threaded through correctly)
testAll :: IO ()
testAll = do
  putStrLn $ testBaseline (Proxy :: Proxy "testBaseline")
  putStrLn $ testSimple (Proxy :: Proxy "testSimple")
  putStrLn $ testCall1 (Proxy :: Proxy "testCall1")
  putStrLn $ testCall2 (Proxy :: Proxy "testCall2")
  putStrLn $ testSimples1 (Proxy :: Proxy "testSimples1")
  putStrLn $ testSimples2 (Proxy :: Proxy "testSimples2")
  putStrLn $ testSimples3 (Proxy :: Proxy "testSimples3 arg 1,") (Proxy :: Proxy "testSimples3 arg 2")
  putStrLn $ testSimples4 (Proxy :: Proxy "testSimples4 arg 1,") (Proxy :: Proxy "testSimples4 arg 2")
  putStrLn $ testSimples5 (Proxy :: Proxy "testSimples5 arg 1,") (Proxy :: Proxy "testSimples5 arg 2")
  putStrLn $ testSimples6 (Proxy :: Proxy "testSimples6 arg 1,") (Proxy :: Proxy "testSimples6 arg 2")
  putStrLn $ testCalls1 (Proxy :: Proxy "testCalls1")
  putStrLn $ testCalls2 (Proxy :: Proxy "testCalls2")
  putStrLn $ testCalls3 (Proxy :: Proxy "testCalls3 arg 1,") (Proxy :: Proxy "testCalls3 arg 2")
  putStrLn $ testCalls4 (Proxy :: Proxy "testCalls4 arg 1,") (Proxy :: Proxy "testCalls4 arg 2")
  putStrLn $ testCalls5 (Proxy :: Proxy "testCalls5 arg 1,") (Proxy :: Proxy "testCalls5 arg 2")
  putStrLn $ testCalls6 (Proxy :: Proxy "testCalls6 arg 1,") (Proxy :: Proxy "testCalls6 arg 2")
  putStrLn $ testCalls'1 (Proxy :: Proxy "testCalls'1")
  putStrLn $ testCalls'2 (Proxy :: Proxy "testCalls'2")
  putStrLn $ testCalls'3 (Proxy :: Proxy "testCalls'3 arg 1,") (Proxy :: Proxy "testCalls'3 arg 2")
  putStrLn $ testCalls'4 (Proxy :: Proxy "testCalls'4 arg 1,") (Proxy :: Proxy "testCalls'4 arg 2")
  putStrLn $ testCalls'5 (Proxy :: Proxy "testCalls'5 arg 1,") (Proxy :: Proxy "testCalls'5 arg 2")
  putStrLn $ testCalls'6 (Proxy :: Proxy "testCalls'6 arg 1,") (Proxy :: Proxy "testCalls'6 arg 2")
  putStrLn $ testWeirdOrderSimples (Proxy :: Proxy "testWeirdOrderSimples arg 1,") (Proxy :: Proxy "testWeirdOrderSimples arg 2")
  putStrLn $ testWeirdOrderCalls1 (Proxy :: Proxy "testWeirdOrderCalls1 arg 1,") (Proxy :: Proxy "testWeirdOrderCalls1 arg 2")
  putStrLn $ testWeirdOrderCalls2 (Proxy :: Proxy "testWeirdOrderCalls2 arg 1,") (Proxy :: Proxy "testWeirdOrderCalls2 arg 2")
  putStrLn $ testWeirdOrderCalls3 (Proxy :: Proxy "testWeirdOrderCalls3 arg 1,") (Proxy :: Proxy "testWeirdOrderCalls3 arg 2")
  putStrLn $ testPolyCastCall1 (Proxy :: Proxy "testPolyCastCall1")
  putStrLn $ testPolyCastCall2 (Proxy :: Proxy "testPolyCastCall2")
  putStrLn $ testMonoCastCall1 (Proxy :: Proxy "testMonoCastCall1")
  putStrLn $ testMonoCastCall2 (Proxy :: Proxy "testMonoCastCall2")
  putStrLn $ testPolyCastCall'1 (Proxy :: Proxy "testPolyCastCall'1")
  putStrLn $ testPolyCastCall'2 (Proxy :: Proxy "testPolyCastCall'2")
  putStrLn $ testMonoCastCall'1 (Proxy :: Proxy "testMonoCastCall'1")
  putStrLn $ testMonoCastCall'2 (Proxy :: Proxy "testMonoCastCall'2")
  putStrLn $ testEtaSimple (Proxy :: Proxy "testEtaSimple")
  putStrLn $ testEtaCall1 (Proxy :: Proxy "testEtaCall1")
  putStrLn $ testEtaCall2 (Proxy :: Proxy "testEtaCall2")
  putStrLn $ testNestedPolySimple (Proxy :: Proxy "testNestedPolySimple")
  putStrLn $ testNestedMonoSimple (Proxy :: Proxy "testNestedMonoSimple")
  putStrLn $ testNestedInferredSimple (Proxy :: Proxy "testNestedInferredSimple")
  putStrLn $ testNestedPolyCall1 (Proxy :: Proxy "testNestedPolyCall1")
  putStrLn $ testNestedPolyCall2 (Proxy :: Proxy "testNestedPolyCall2")
  putStrLn $ testNestedPolyCall3 (Proxy :: Proxy "testNestedPolyCall3")
  putStrLn $ testNestedMonoCall (Proxy :: Proxy "testNestedMonoCall")
  putStrLn $ testNestedInferredCall1 (Proxy :: Proxy "testNestedInferredCall1")
  putStrLn $ testNestedInferredCall2 (Proxy :: Proxy "testNestedInferredCall2")
  putStrLn $ testLambdaSimple (Proxy :: Proxy "testLambdaSimple")
  putStrLn $ testLambdaCall1 (Proxy :: Proxy "testLambdaCall1")
  putStrLn $ testLambdaCall2 (Proxy :: Proxy "testLambdaCall2")
  putStrLn $ testExpAppSimple (Proxy :: Proxy "testExpAppSimple")
  putStrLn $ testExpAppCall1 (Proxy :: Proxy "testExpAppCall1")
  putStrLn $ testExpAppCall2 (Proxy :: Proxy "testExpAppCall2")
  putStrLn $ testExpAppCalls'1 (Proxy :: Proxy "testExpAppCalls'1")
  putStrLn $ testExpAppCalls'2 (Proxy :: Proxy "testExpAppCalls'2")
  putStrLn $ testExpAppCalls'3 (Proxy :: Proxy "testExpAppCalls'3 arg 1,") (Proxy :: Proxy "testExpAppCalls'3 arg 2")
  putStrLn $ testExpAppCalls'4 (Proxy :: Proxy "testExpAppCalls'4 arg 1,") (Proxy :: Proxy "testExpAppCalls'4 arg 2")
  putStrLn $ testExpAppCalls'5 (Proxy :: Proxy "testExpAppCalls'5 arg 1,") (Proxy :: Proxy "testExpAppCalls'5 arg 2")
  putStrLn $ testExpAppCalls'6 (Proxy :: Proxy "testExpAppCalls'6 arg 1,") (Proxy :: Proxy "testExpAppCalls'6 arg 2")
  putStrLn $ testArgBeforeTy () (Proxy :: Proxy "testArgBeforeTy")
  putStrLn $ testArgBeforeTy' (Proxy :: Proxy "testArgBeforeTy'")
  putStrLn $ testNestedEtaSimple (Proxy :: Proxy "testNestedEtaSimple")
  putStrLn $ testNestedEtaCall1 (Proxy :: Proxy "testNestedEtaCall1")
  putStrLn $ testNestedEtaCall2 (Proxy :: Proxy "testNestedEtaCall2")
  putStrLn $ testRankNCall
  putStrLn $ testTypeAbsCall1 @"testTypeAbsCall1"
  putStrLn $ testTypeAbsCall2 (Proxy :: Proxy "testTypeAbsCall2")
  print $ testTypeAliasCall ((2 :: Int) :> VNil)
  print $ testReducibleTypeFamilyCall ((2 :: Int) :> VNil)
  print $ testIrreducibleTypeFamilyCall (Proxy :: Proxy (S (S Z))) ((2 :: Int) :> VNil)
  print $ testListOfFalse (Proxy :: Proxy (S Z))
  print $ testListOfMempty (Proxy :: Proxy (S (S Z))) (Proxy :: Proxy (Sum Int))
  print $ vlength ((2 :: Int) :> 3 :> VNil)
  print $ sumLengths (VLCons ("a" :> VNil) (VLCons ("b" :> "c" :> VNil) (VLCons ("d" :> VNil) VLNil)))
  print $ sumLengthsInline [VecSomeLength ("a" :> VNil), VecSomeLength ("b" :> "c" :> VNil), VecSomeLength ("d" :> VNil)]
  print $ letExistential WrappedIsNat ("a" :> VNil)
  -- putStrLn $ f @(S Z) @(S (S Z))
  return ()
