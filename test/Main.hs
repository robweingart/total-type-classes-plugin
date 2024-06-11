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
  --putStrLn $ testExposed (Proxy :: Proxy "testExposed")
  --putStrLn $ testExposedCall (Proxy :: Proxy "testExposedCall")
  Check.testAll
  --TestModule.testAll
  return ()
