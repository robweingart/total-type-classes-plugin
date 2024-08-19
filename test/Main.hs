{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Data.Proxy
import TotalClassPlugin
import qualified Check
--import qualified Partial
--import qualified TestModule

$mkSecretThing

main :: IO ()
main = do
  putStrLn $ secret
  --putStrLn $ TestModule.testExposedSimple (Proxy :: Proxy "testExposedSimple")
  --putStrLn $ TestModule.testExposedCall1 (Proxy :: Proxy "testExposedCall1")
  --putStrLn $ TestModule.testExposedCall2 (Proxy :: Proxy "testExposedCall2")
  --TestModule.testAll
  Check.testAll
  --Partial.foo2
  return ()
