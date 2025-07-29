{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module TotalClassPlugin.Checker.CM ( CheckResult, CheckState, CM, CheckName (..), successfulResult, failCM, maybeFailCM, runCM, liftTcM, getOriginalConstraint ) where

import GHC.Tc.Types (TcM)
import TotalClassPlugin.Checker.Errors (failWithTotal, TotalFailureDetails)
import Control.Monad.State (StateT (..), get, MonadState (..), lift)
import Control.Monad.Reader (ReaderT (runReaderT), MonadReader (ask))
import GHC (PredType)

type CheckResult = (Bool, Bool, Bool)
data CheckState = FailOnError | CollectErrors CheckResult
type CM a = ReaderT PredType (StateT CheckState TcM) a
data CheckName = Exhaustiveness | Termination | Context

successfulResult :: CheckResult
successfulResult = (True, True, True)

liftTcM :: TcM a -> CM a
liftTcM = lift . lift

getOriginalConstraint :: CM PredType
getOriginalConstraint = ask

failCM :: CheckName -> TotalFailureDetails -> CM ()
failCM which details = get >>= \case
  FailOnError -> do
    original <- ask
    liftTcM $ failWithTotal original details
  CollectErrors (ex, term, cxt) -> put $ case which of
    Exhaustiveness -> CollectErrors (False, term, cxt)
    Termination -> CollectErrors (ex, False, cxt)
    Context -> CollectErrors (ex, term, False)

maybeFailCM :: CheckName -> Maybe TotalFailureDetails -> CM ()
maybeFailCM _ Nothing = return ()
maybeFailCM which (Just details) = failCM which details

runCM :: Bool -> PredType -> CM () -> TcM CheckResult
runCM fail_on_err original thing_inside = runStateT (runReaderT thing_inside original) initial >>= \case 
  ((), FailOnError) -> return successfulResult
  ((), CollectErrors res) -> return res
  where
    initial = if fail_on_err then FailOnError else CollectErrors successfulResult
