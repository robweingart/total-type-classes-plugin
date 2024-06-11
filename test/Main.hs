{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Data.Proxy
import qualified Check
import qualified TestModule

main :: IO ()
main = do
  putStrLn $ TestModule.testExposed (Proxy :: Proxy "testExposed")
  putStrLn $ TestModule.testExposedCall (Proxy :: Proxy "testExposedCall")
  TestModule.testAll
  --Check.testAll
  return ()
