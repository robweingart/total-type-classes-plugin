{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import qualified Checker
import Data.Proxy
import qualified Partial
import qualified Rewriter

main :: IO ()
main = do
  -- Call some functions defined in another module
  putStrLn $ Rewriter.testExposedSimple (Proxy :: Proxy "testExposedSimple")
  putStrLn $ Rewriter.testExposedCall1 (Proxy :: Proxy "testExposedCall1")
  putStrLn $ Rewriter.testExposedCall2 (Proxy :: Proxy "testExposedCall2")
  Rewriter.testAll
  Checker.testAll
  print Partial.foo2
  return ()
