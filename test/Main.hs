{-# OPTIONS_GHC -fplugin=TestPlugin.Plugin #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Data.Proxy
import TestPlugin

class MyTotalClass (a :: Bool) where
  isTrue :: Proxy a -> Bool

instance TotalClass MyTotalClass where
  totalityEvidence = assertTotality

-- f1 :: a -> m a
-- f1 x = return x
-- 
-- f2 :: a -> a -> a
-- f2 = (+)

g x = x * 2

f :: forall (a :: Bool). MyTotalClass a => Proxy a -> Bool
f x = isTrue x

main :: IO ()
main = putStrLn "Test suite not yet implemented."
