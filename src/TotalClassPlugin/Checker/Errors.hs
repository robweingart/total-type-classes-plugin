{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
module TotalClassPlugin.Checker.Errors where

import GHC.Plugins
import GHC.HsToCore.Pmc.Types (Nabla)
import GHC.HsToCore.Errors.Types (ExhaustivityCheckType, MaxUncoveredPatterns, DsMessage (DsNonExhaustivePatterns))
import GHC (GhcTc)
import GHC.Hs.Expr (HsMatchContext (..))
import GHC.Tc.Errors.Types (TcRnMessage (..), mkTcRnUnknownMessage, TcRnMessageDetailed (..), THError (ReportCustomQuasiError))
import GHC.Tc.Types (TcRn, TcM)
import GHC.Tc.Utils.Monad (addMessages, failWithTc, tryTc)
import GHC.Utils.Error (Diagnostic (..), noHints)
import GHC.Types.Error (mkSimpleDecorated, NoDiagnosticOpts (NoDiagnosticOpts), unionDecoratedSDoc, HasDefaultDiagnosticOpts (defaultOpts), MsgEnvelope (..), Messages (..))
import GHC.Data.Bag (mapMaybeBag, headMaybe, partitionBagWith)
import GHC.Core.Class (Class (..))
import TotalClassPlugin.Rewriter.Utils
import Language.Haskell.TH (Q)
import GHC.Tc.Gen.Splice (runQuasi)

data TotalClassCheckerMessage = TotalNonExhaustive !(HsMatchContext GhcTc) !ExhaustivityCheckType !MaxUncoveredPatterns [Id] [Nabla]
                              | TotalNonTerminating TcRnMessage
                              | TotalCheckerTHFailure String
                              | TotalCheckerTHFatal THError
                              | TotalCheckerInvalidContext Type PredType
                              | TotalError

instance Diagnostic TotalClassCheckerMessage where
  type DiagnosticOpts TotalClassCheckerMessage = NoDiagnosticOpts
  diagnosticMessage _ = \case
    TotalNonExhaustive cxt flag max_p ids nablas ->
      mkSimpleDecorated (text "Exhaustiveness check failed:") `unionDecoratedSDoc` diagnosticMessage NoDiagnosticOpts (DsNonExhaustivePatterns cxt flag max_p ids nablas)
    TotalNonTerminating tc_msg ->
      mkSimpleDecorated (text "Termination check failed:") `unionDecoratedSDoc` diagnosticMessage defaultOpts tc_msg
    TotalCheckerTHFailure str ->
      mkSimpleDecorated (text "Exhaustiveness check failed:" $$ text str)
    TotalCheckerTHFatal err -> mkSimpleDecorated (text "Unexpected fatal error during exhaustiveness check code gen:") `unionDecoratedSDoc` diagnosticMessage defaultOpts (TcRnTHError err)
    TotalCheckerInvalidContext tau pred_ty -> mkSimpleDecorated (text "Invalid constraint" <+> ppr pred_ty <+> text "in instance with head" <+> ppr tau)
    TotalError -> mkSimpleDecorated $ text "Unexpected error"

  diagnosticReason _ = ErrorWithoutFlag
  diagnosticHints _ = noHints
  diagnosticCode _ = Nothing

failWithTotal :: TotalClassCheckerMessage -> TcM a
failWithTotal = failWithTc . mkTcRnUnknownMessage

checkQuasiError :: Q a -> TcM (Either TotalClassCheckerMessage a)
checkQuasiError thing_inside = do
  (result, msgs) <- tryTc $ runQuasi thing_inside 
  case result of
    Just x -> return $ Right x
    Nothing -> do
      let (fatal, check_failure) = partitionBagWith get_th_msg $ mapMaybeBag get_th_error $ getMessages msgs
      case (headMaybe fatal, headMaybe check_failure) of
        (Nothing, Nothing) -> failWithTotal TotalError
        (Just e, _) -> failWithTotal e
        (Nothing, Just reason) -> return (Left reason)
  where
    get_th_error (MsgEnvelope{errMsgDiagnostic=tc_msg}) = case tc_msg of
      TcRnTHError err -> Just err
      (TcRnMessageWithInfo _ (TcRnMessageDetailed _ (TcRnTHError err))) -> Just err
      _ -> Nothing

    get_th_msg (ReportCustomQuasiError True str) = Right (TotalCheckerTHFailure str)
    get_th_msg e = Left (TotalCheckerTHFatal e)

checkTcRnResult :: TcRn (Maybe a, Messages TcRnMessage) -> TcRn a
checkTcRnResult thing_inside = do
  (result, msgs) <- thing_inside
  case result of
    Just x -> return x
    Nothing -> do
      addMessages msgs
      failWithTotal TotalError

checkDsResult :: Class -> TcM (Messages DsMessage, Maybe a) -> TcM (Maybe TotalClassCheckerMessage)
checkDsResult cls thing_inside = do
  (msgs, result) <- thing_inside
  case result of
    Nothing -> do
      addMessages (fmap mkTcRnUnknownMessage msgs)
      failWithTotal TotalError
    Just _ -> do
      let non_exhaustive_msgs = mapMaybeBag get_non_exhaustive_msg $ getMessages msgs
      return $ headMaybe non_exhaustive_msgs
  where
    get_non_exhaustive_msg (MsgEnvelope{errMsgDiagnostic=(DsNonExhaustivePatterns cxt@FunRhs{mc_fun=(L l name)} flag maxPatterns vars nablas)}) = Just ds_msg
      where
        occ_name = mkOccName (nameNameSpace name) $ "the exhaustiveness check for " ++ (occNameString $ nameOccName $ className cls)
        new_name = tidyNameOcc name occ_name
        ds_msg = TotalNonExhaustive (cxt{mc_fun=(L l new_name)}) flag maxPatterns vars nablas
    get_non_exhaustive_msg _ = Nothing

checkPaterson :: TcM (Maybe a, Messages TcRnMessage) -> TcM (Maybe TotalClassCheckerMessage)
checkPaterson thing_inside = do
  (result, msgs) <- thing_inside
  case result of
    Just _ -> return Nothing
    Nothing -> do
      let paterson_msgs = mapMaybeBag get_paterson_msg $ getMessages msgs
      case headMaybe paterson_msgs of
        Nothing -> do
          addMessages msgs
          failWithTotal TotalError
        Just paterson_msg -> return $ Just paterson_msg
  where
    get_paterson_msg (MsgEnvelope{errMsgDiagnostic=tc_msg}) = case tc_msg of
      (TcRnPatersonCondFailure{}) -> Just (TotalNonTerminating tc_msg)
      (TcRnMessageWithInfo _ (TcRnMessageDetailed _ inner_msg@(TcRnPatersonCondFailure{}))) -> Just (TotalNonTerminating inner_msg)
      _ -> Nothing
