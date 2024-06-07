{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Data.Proxy
import TestModule

main :: IO ()
main = do
  putStrLn $ testExposed (Proxy :: Proxy "testExposed")
  putStrLn $ testExposedCall (Proxy :: Proxy "testExposedCall")
  testAll
  return ()
