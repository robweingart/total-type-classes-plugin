{-# OPTIONS_GHC -fplugin=TestPlugin.Plugin #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module TestModule where

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

f2 :: forall (a :: Bool). Proxy a -> Bool
f2 x = isTrue x && isTrue x

fWeird :: forall (a :: Bool). MyTotalClass a => forall (b :: Bool). Proxy a -> Proxy b -> Bool
fWeird x y = isTrue x && isTrue y

--fEta  :: forall (a :: Bool). Proxy a -> Bool
--fEta = isTrue
--
--
f' :: forall (a :: Bool). MyTotalClass a => Proxy a -> Bool
f' x = isTrue x

f2' :: forall (a :: Bool). MyTotalClass a => Proxy a -> Bool
f2' x = isTrue x && isTrue x
--
--fMono ::  Bool
--fMono = isTrue (Proxy :: Proxy True)
--
--showF :: forall (a :: Bool). Proxy a -> String
--showF x = show $ f x
--
showFWeird :: forall (a :: Bool) (b :: Bool). Proxy a -> Proxy b -> String
showFWeird x y = show $ fWeird x y
--
--showFF :: forall (a :: Bool). Proxy a -> String
--showFF x = show (f x) ++ show (f x) 
--
--showF2 :: forall (a :: Bool). Proxy a -> String
--showF2 x = show $ fAnd x
--  where 
--    fAnd :: forall (b :: Bool). Proxy b -> Bool
--    fAnd y = isTrue y && isTrue y

--showFAnd :: forall (a :: Bool). Proxy a -> String
--showFAnd x = show $ fAnd x
--  where 
--    --fAnd :: forall (b :: Bool). Proxy b -> Bool
--    fAnd y = f y && f y
--
--showFMono :: String
--showFMono = show $ f (Proxy :: Proxy True)


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

--vlength :: Vec n a -> MyNat
--vlength (_ :: Vec n a) = natTerm @n
