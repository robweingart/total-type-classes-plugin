{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fplugin=TotalClassPlugin.Plugin #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Check where

import TotalClassPlugin

data MyNat = Z | S MyNat

class IsNat (n :: MyNat) where

instance IsNat Z where
instance IsNat n => IsNat (S n) where

class C (x :: MyNat) (y :: MyNat) where

instance C Z Z where

instance C Z y => C Z (S y) where

instance C x y => C (S x) y

class C' (n :: MyNat) where

instance C' Z where

instance C' (S Z) where

instance C' n => C' (S (S n)) where

class CNonTerm (n :: MyNat) where

instance CNonTerm Z
instance CNonTerm (S n) => CNonTerm (S n)

-- $(mkEvidenceFun ''IsNat [True])

-- $(mkEvidenceFun ''C [True, True])
-- 
-- $(mkEvidenceFun ''C' [True])

instance TotalClass IsNat where
  totalityEvidence = checkTotality 

instance TotalClass C' where
  totalityEvidence = checkTotality 

--instance TotalClass CNonTerm where
--  totalityEvidence = checkTotality 
