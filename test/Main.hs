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
  print $ f (Proxy :: Proxy True)
  print $ fMono
  print $ showF (Proxy :: Proxy True)
  print $ showFMono
  print $ vlength $ VCons "hello" $ VCons "world" VNil
  putStrLn "Test suite not yet implemented."

-- f1 :: a -> m a
-- f1 x = return x
-- 
-- f2 :: a -> a -> a
-- f2 = (+)

--test :: forall k (c :: k -> Constraint). TotalClass c => String
--test = show $ totalityEvidence @k @c
--
--test2 = test @Bool @MyTotalClass
