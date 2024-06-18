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
  putStrLn $ TestModule.testExposedSimple (Proxy :: Proxy "testExposedSimple")
  putStrLn $ TestModule.testExposedCall1 (Proxy :: Proxy "testExposedCall1")
  putStrLn $ TestModule.testExposedCall2 (Proxy :: Proxy "testExposedCall2")
  TestModule.testAll
  Check.testAll
  return ()
