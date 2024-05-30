{-# OPTIONS_GHC -fplugin=TestPlugin.Plugin #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Data.Proxy
import TestPlugin

class MyTotalClass (a :: Bool) where
  isTrue :: Proxy a -> Bool

instance TotalClass MyTotalClass where
  totalityEvidence = assertTotality
--
f :: forall (a :: Bool). Show String => Bool -> Proxy a -> Bool
f True x = isTrue x
f False x = isTrue x && isTrue x

f' :: forall (a :: Bool). (MyTotalClass a, Show String) => Bool -> Proxy a -> Bool
f' True x = isTrue x
f' False x = isTrue x && isTrue x


main :: IO ()
main = do
  --putStrLn $ show $ f True (Proxy :: Proxy True)
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
