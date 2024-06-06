{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Checking where

import Data.Constraint
import Data.Singletons
import Data.Singletons.TH
import TestPlugin

data MyNat = Z | S MyNat deriving Show

class IsNat (n :: MyNat) where
  natTerm :: MyNat

instance IsNat Z where
  natTerm = Z

instance IsNat n => IsNat (S n) where
  natTerm = S (natTerm @n)

instance TotalClass IsNat where
  totalityEvidence = assertTotality

evFun2 :: MyNat -> MyNat -> ()
evFun2 Z Z = ()
evFun2 (S x) Z = evFun2 x Z
evFun2 Z (S y) = evFun2 y Z
evFun2 (S x) (S y) = evFun2 x y

$(genSingletons [''MyNat])

data WhichChecks = ExhaustivenessOnly | SimpleTermination | NoCheck

data ChecksEvidence (wc :: WhichChecks) = UnsafeChecksEvidence

class GenTotalityCheck c (wc :: WhichChecks) | c -> wc where
  totalFun :: Sing a -> Dict (c a)
  totalEvidence :: ChecksEvidence wc

totalInst :: (GenTotalityCheck c wc) => SingI a :- c a
totalInst = Sub (totalFun sing)

evFun :: MyNat -> ()
evFun Z = undefined
evFun (S n) = evFun Z

instance GenTotalityCheck IsNat NoCheck where
  totalFun sn = case sn of
    SZ -> instZ
    SS sn' -> mapDict instS (totalFun sn')
    where
      instZ :: Dict (IsNat Z)
      instZ = Dict
      instS :: IsNat n :- IsNat (S n)
      instS = Sub Dict
  totalEvidence = UnsafeChecksEvidence

instance {-# OVERLAPPABLE #-} SingI n => IsNat n where
  natTerm = natTerm @n \\ totalFun @IsNat (sing @n)

class MyClass2 (x :: MyNat) (y :: MyNat)

instance MyClass2 Z Z

instance (MyClass2 x Z) => MyClass2 (S x) Z

instance (MyClass2 Z y) => MyClass2 Z (S y)

instance (MyClass2 x y) => MyClass2 (S x) (S y)

--instance GenTotalityCheck MyClass2 NoCheck where
--  totalFun sn = case sn of
--    SZ -> instZ
--    SS sn' -> mapDict instS (totalFun sn')
--    where
--      instZ :: Dict (IsNat Z)
--      instZ = Dict
--      instS :: IsNat n :- IsNat (S n)
--      instS = Sub Dict
--  totalEvidence = UnsafeChecksEvidence
