{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module TotalClassPlugin.Checker.CM ( CheckResult, CheckState, CM, CheckName (..), successfulResult, failCM, maybeFailCM, runCM ) where

import GHC.Tc.Types (TcM)
import TotalClassPlugin.Checker.Errors (TotalClassCheckerMessage (..), failWithTotal)
import Control.Monad.State (StateT (..), get, MonadState (..), lift)

type CheckResult = (Bool, Bool, Bool)
data CheckState = FailOnError | CollectErrors CheckResult
type CM a = StateT CheckState TcM a
data CheckName = Exhaustiveness | Termination | Context

successfulResult :: CheckResult
successfulResult = (True, True, True)

failCM :: CheckName -> TotalClassCheckerMessage -> CM ()
failCM which message = get >>= \case
  FailOnError -> lift $ failWithTotal message
  CollectErrors (ex, term, cxt) -> put $ case which of
    Exhaustiveness -> CollectErrors (False, term, cxt)
    Termination -> CollectErrors (ex, False, cxt)
    Context -> CollectErrors (ex, term, False)

maybeFailCM :: CheckName -> Maybe TotalClassCheckerMessage -> CM ()
maybeFailCM _ Nothing = return ()
maybeFailCM which (Just message) = failCM which message

runCM :: Bool -> CM () -> TcM CheckResult
runCM fail_on_err thing_inside = runStateT thing_inside initial >>= \case 
  ((), FailOnError) -> return successfulResult
  ((), CollectErrors res) -> return res
  where
    initial = if fail_on_err then FailOnError else CollectErrors successfulResult
