{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}

module TestPlugin ( TotalityEvidence, CheckTotality(..), assertTotality, TotalClass(..) ) where

import Data.Kind

data TotalityEvidence (c :: k -> Constraint) where UnsafeTotalityEvidence :: TotalityEvidence c deriving Show

assertTotality :: TotalityEvidence c
assertTotality = UnsafeTotalityEvidence

class CheckTotality (c :: k -> Constraint) where
  checkTotality :: TotalityEvidence c

class TotalClass (c :: k -> Constraint) where
  totalityEvidence :: TotalityEvidence c
