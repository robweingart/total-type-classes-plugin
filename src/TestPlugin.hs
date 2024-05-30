{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}

module TestPlugin ( TotalityEvidence, CheckTotality(..), assertTotality, TotalClass(..) ) where

import Data.Kind

class IsClassKind c where

instance IsClassKind Constraint where

instance IsClassKind c => IsClassKind (a -> c)

data TotalityEvidence c where UnsafeTotalityEvidence :: TotalityEvidence c deriving Show

assertTotality :: IsClassKind ck => TotalityEvidence (c :: ck)
assertTotality = UnsafeTotalityEvidence

class IsClassKind ck => CheckTotality (c :: ck) where
  checkTotality :: TotalityEvidence c

class IsClassKind ck => TotalClass (c :: ck) where
  totalityEvidence :: TotalityEvidence c
