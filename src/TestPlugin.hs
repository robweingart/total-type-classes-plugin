{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}

module TestPlugin ( Totality(..), TotalClass(..) ) where

import Data.Kind

data Totality = Total | AssertTotal | Partial

class TotalClass (a :: k -> Constraint) where
  totality :: Totality
