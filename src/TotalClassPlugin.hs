{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module TotalClassPlugin ( TotalityEvidence, CheckTotality(..), CheckTotalityResult(..), assertTotality, TotalClass(..) ) where

import Data.Kind (Constraint)
import qualified Data.Kind

class IsClassKind c where

instance IsClassKind Constraint where

instance IsClassKind c => IsClassKind (a -> c)

data TotalityEvidence c where UnsafeTotalityEvidence :: TotalityEvidence c deriving Show

assertTotality :: IsClassKind ck => TotalityEvidence (c :: ck)
assertTotality = UnsafeTotalityEvidence

--data CheckExhaustiveness = ViaPmc | AssertExhaustiveness
--
--data CheckTermination = ViaPaterson | AssertTermination
--
--data CheckerOptions = COpt CheckExhaustiveness CheckTermination

--type family ResultEvidence c (r :: CheckerResult) :: Type where
--  ResultEvidence c CheckerSuccess = TotalityEvidence c
--  ResultEvidence _ _ = ()

type CheckTotalityResult :: forall {ck :: Data.Kind.Type}. ck -> Constraint
class CheckTotalityResult (c :: ck) where
  isExhaustive :: Bool
  isTerminating :: Bool
  isContextOk :: Bool

--class IsClassKind ck => CheckTotality (c :: ck) where
type CheckTotality :: forall {ck :: Data.Kind.Type}. ck -> Constraint
class CheckTotality (c :: ck) where
  checkTotality :: TotalityEvidence c

--instance (CheckTotalityResult c opt CheckerSuccess) => CheckTotality c opt where
--  checkTotality = resultEvidence @c @opt

class IsClassKind ck => TotalClass (c :: ck) where
  totalityEvidence :: TotalityEvidence c
