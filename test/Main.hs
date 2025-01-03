{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Main (main) where

import Data.Proxy
import qualified Check
import qualified Partial
import qualified TestModule

data MyNat = Z | S MyNat deriving Show

class C (x :: MyNat) (y :: MyNat) where
  showN :: String
instance C Z y where
  showN = ""
instance C n y => C (S n) y where
  showN = "." ++ showN @n @y

--f :: forall (m :: MyNat) (n :: MyNat). C m (S n) => String
f (Proxy :: Proxy m) (Proxy :: Proxy n) =  showN @m @n ++ f (Proxy :: Proxy (S m)) (Proxy :: Proxy (S n))

main :: IO ()
main = do
  putStrLn $ TestModule.testExposedSimple (Proxy :: Proxy "testExposedSimple")
  putStrLn $ TestModule.testExposedCall1 (Proxy :: Proxy "testExposedCall1")
  putStrLn $ TestModule.testExposedCall2 (Proxy :: Proxy "testExposedCall2")
  TestModule.testAll
  Check.testAll
  putStrLn $ show $ Partial.foo2
  return ()
