{-# OPTIONS_GHC -fplugin=TestPlugin.Plugin #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module Main (main) where

import TestPlugin

class MyTotalClass (a :: Bool) where
  isTrue :: Bool

instance TotalClass MyTotalClass where
  totality = Total

main :: IO ()
main = putStrLn "Test suite not yet implemented."
