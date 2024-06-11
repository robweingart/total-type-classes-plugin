{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Check where

import TotalClassPlugin
import Control.Exception (evaluate, assert)

data MyNat = Z | S MyNat

class IsNat (n :: MyNat) where

instance IsNat Z where
instance IsNat n => IsNat (S n) where

class C (x :: MyNat) (y :: MyNat) where

instance C Z Z where

instance C Z y => C Z (S y) where

instance C x y => C (S x) y

class CNonEx (n :: MyNat) where

instance CNonEx Z where

--instance CNonEx (S Z) where

instance CNonEx n => CNonEx (S (S n)) where

class CNonTerm (n :: MyNat) where

instance CNonTerm Z
instance CNonTerm (S n) => CNonTerm (S n)

-- $(mkEvidenceFun ''IsNat [True])

-- $(mkEvidenceFun ''C [True, True])
-- 
-- $(mkEvidenceFun ''CNonEx [True])

instance TotalClass IsNat where
  totalityEvidence = checkTotality 

testGood :: IO ()
testGood = do
  evaluate $ assert (isExhaustive @C) ()
  evaluate $ assert (isTerminating @C) ()

testNonEx :: IO ()
testNonEx = do
  evaluate $ assert (not $ isExhaustive @CNonEx) ()
  evaluate $ assert (isTerminating @CNonEx) ()

testNonTerm :: IO ()
testNonTerm = do
  evaluate $ assert (isExhaustive @CNonTerm) ()
  evaluate $ assert (not $ isTerminating @CNonTerm) ()

testAll :: IO ()
testAll = do
  testGood
  testNonEx
  testNonTerm
