{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module TestPlugin ( TotalityEvidence, CheckTotality(..), assertTotality, TotalClass(..) ) where

import Data.Kind
import GHC.TypeNats (Nat, type (+))

class IsClassKind (n :: Nat) ck | ck -> n where
  type ArgKinds ck :: [Type]

instance IsClassKind 0 Constraint where
  type ArgKinds Constraint = '[]

instance IsClassKind n ck => IsClassKind (n + 1) (k -> ck) where
  type ArgKinds (k -> ck) = (k ': ArgKinds ck)

data TotalityEvidence c where UnsafeTotalityEvidence :: TotalityEvidence c deriving Show

assertTotality :: IsClassKind ck => TotalityEvidence (c :: ck)
assertTotality = UnsafeTotalityEvidence

class IsClassKind ck => CheckTotality (c :: ck) where
  checkTotality :: TotalityEvidence c

class IsClassKind ck => TotalClass (c :: ck) where
  totalityEvidence :: TotalityEvidence c
