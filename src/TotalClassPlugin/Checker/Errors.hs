{-# LANGUAGE TypeFamilies #-}

module TotalClassPlugin.Checker.Errors where

import GHC (HsMatchContextRn)
import GHC.Core.Class (Class (..))
import GHC.Data.Bag (headMaybe, mapMaybeBag, partitionBagWith)
import GHC.Hs.Expr (HsMatchContext (..))
import GHC.HsToCore.Errors.Types (DsMessage (DsNonExhaustivePatterns), ExhaustivityCheckType, MaxUncoveredPatterns)
import GHC.HsToCore.Pmc.Types (Nabla)
import GHC.Plugins
import GHC.Tc.Errors.Types (THError (ReportCustomQuasiError), TcRnMessage (..), TcRnMessageDetailed (..), mkTcRnUnknownMessage)
import GHC.Tc.Gen.Splice (runQuasi)
import GHC.Tc.Types (TcM, TcRn)
import GHC.Tc.Utils.Monad (addMessages, failWithTc, tryTc)
import GHC.Tc.Utils.TcType (PatersonCondFailure, PatersonCondFailureContext (InInstanceDecl))
import GHC.Types.Error (DecoratedSDoc, HasDefaultDiagnosticOpts (defaultOpts), Messages (..), MsgEnvelope (..), NoDiagnosticOpts (NoDiagnosticOpts), mkSimpleDecorated, unionDecoratedSDoc)
import GHC.Utils.Error (Diagnostic (..), noHints)
import Language.Haskell.TH (Q)

data TotalClassCheckerMessage
  = TotalClassCheckerMessage {tcc_msg_original :: PredType, tcc_msg_details :: TotalFailureDetails}

totalClassCheckerMessage :: PredType -> TotalFailureDetails -> TotalClassCheckerMessage
totalClassCheckerMessage original details = TotalClassCheckerMessage { tcc_msg_original = original, tcc_msg_details = details }

data TotalFailureDetails
  = TotalNonExhaustive !HsMatchContextRn !ExhaustivityCheckType !MaxUncoveredPatterns [Id] [Nabla]
  | TotalTHFailure String
  | TotalTHFatal TcRnMessage
  | TotalContextEscapes {tcc_msg_inst_head :: PredType, tcc_msg_wanted :: PredType}
  | TotalContextNotSmaller {tcc_msg_inst_head :: PredType, tcc_msg_wanted :: PredType, tcc_msg_paterson_pcf :: PatersonCondFailure}
  | TotalContextNotSolved {tcc_msg_inst_head :: PredType, tcc_msg_err :: TcRnMessage}
  | TotalError

ppr_details :: TotalFailureDetails -> DecoratedSDoc
ppr_details (TotalNonExhaustive cxt flag max_p ids nablas) =
  diagnosticMessage NoDiagnosticOpts (DsNonExhaustivePatterns cxt flag max_p ids nablas)
ppr_details (TotalTHFailure str) =
  mkSimpleDecorated (text "Exhaustiveness check failed:" $$ text str)
ppr_details (TotalTHFatal tc_msg) = mkSimpleDecorated (text "Unexpected fatal error during exhaustiveness check code gen:") `unionDecoratedSDoc` diagnosticMessage defaultOpts tc_msg
ppr_details (TotalContextEscapes {tcc_msg_inst_head = inst_head, tcc_msg_wanted = wanted}) = mkSimpleDecorated (text "Constraint" <+> ppr wanted <+> text "in context of instance with head" <+> ppr inst_head <+> text "cannot be deduced from total constraint")
ppr_details (TotalContextNotSmaller {tcc_msg_inst_head = inst_head, tcc_msg_wanted = wanted, tcc_msg_paterson_pcf = pcf}) =
  mkSimpleDecorated (text "Cannot prove termination of instance with head" <+> ppr inst_head) `unionDecoratedSDoc` diagnosticMessage defaultOpts (TcRnPatersonCondFailure pcf InInstanceDecl wanted inst_head)
ppr_details (TotalContextNotSolved {tcc_msg_inst_head = inst_head, tcc_msg_err = err}) = mkSimpleDecorated (text "Failed to solve context of instance with head" <+> ppr inst_head) `unionDecoratedSDoc` diagnosticMessage defaultOpts err
ppr_details TotalError = mkSimpleDecorated $ text "Unexpected error"

instance Diagnostic TotalClassCheckerMessage where
  type DiagnosticOpts TotalClassCheckerMessage = NoDiagnosticOpts
  diagnosticMessage _ TotalClassCheckerMessage {tcc_msg_original = original, tcc_msg_details = details} = mkSimpleDecorated (text "Totality check failed for" <+> ppr original) `unionDecoratedSDoc` ppr_details details

  diagnosticReason _ = ErrorWithoutFlag
  diagnosticHints _ = noHints
  diagnosticCode _ = Nothing

failWithTotal :: PredType -> TotalFailureDetails -> TcM a
failWithTotal original details = failWithTc (mkTcRnUnknownMessage (totalClassCheckerMessage original details))

checkQuasiError :: PredType -> Q a -> TcM (Either TotalFailureDetails a)
checkQuasiError original thing_inside = do
  (result, msgs) <- tryTc $ runQuasi thing_inside
  case result of
    Just x -> return $ Right x
    Nothing -> do
      let (fatal, check_failure) = partitionBagWith get_th_msg $ mapMaybeBag get_th_error $ getMessages msgs
      case (headMaybe fatal, headMaybe check_failure) of
        (Nothing, Nothing) -> do
          addMessages msgs
          failWithTotal original TotalError
        (Just e, _) -> failWithTotal original e
        (Nothing, Just reason) -> return (Left reason)
  where
    get_th_error (MsgEnvelope {errMsgDiagnostic = tc_msg}) = case tc_msg of
      TcRnTHError err -> Just err
      (TcRnMessageWithInfo _ (TcRnMessageDetailed _ (TcRnTHError err))) -> Just err
      _ -> Nothing

    get_th_msg (ReportCustomQuasiError True str) = Right (TotalTHFailure str)
    get_th_msg e = Left (TotalTHFatal (TcRnTHError e))

checkTcRnResult :: PredType -> TcRn (Maybe a, Messages TcRnMessage) -> TcRn (Either TotalFailureDetails a)
checkTcRnResult original thing_inside = do
  (result, msgs) <- thing_inside
  case result of
    Just x -> return $ Right x
    Nothing -> do
      let (fatal, check_failure) = partitionBagWith classify_msg $ getMessages msgs
      case (headMaybe fatal, headMaybe check_failure) of
        (Nothing, Nothing) -> do
          addMessages msgs
          failWithTotal original TotalError
        (Just e, _) -> failWithTotal original e
        (Nothing, Just reason) -> return (Left reason)
  where
    conflict_err name = TotalTHFailure ("Variable corresponds to multiple parts of the instance head" ++ occNameString (rdrNameOcc name))
    classify_msg (MsgEnvelope {errMsgDiagnostic = tc_msg}) = case tc_msg of
      TcRnBindingNameConflict name _ -> Right (conflict_err name)
      (TcRnMessageWithInfo _ (TcRnMessageDetailed _ (TcRnBindingNameConflict name _))) -> Right (conflict_err name)
      e -> Left (TotalTHFatal e)

checkDsResult :: PredType -> Class -> TcM (Messages DsMessage, Maybe a) -> TcM (Maybe TotalFailureDetails)
checkDsResult original cls thing_inside = do
  (msgs, result) <- thing_inside
  case result of
    Nothing -> do
      addMessages (fmap mkTcRnUnknownMessage msgs)
      failWithTotal original TotalError
    Just _ -> do
      let non_exhaustive_msgs = mapMaybeBag get_non_exhaustive_msg $ getMessages msgs
      return $ headMaybe non_exhaustive_msgs
  where
    get_non_exhaustive_msg (MsgEnvelope {errMsgDiagnostic = (DsNonExhaustivePatterns cxt@FunRhs {mc_fun = (L l name)} flag maxPatterns vars nablas)}) = Just ds_msg
      where
        occ_name = mkOccName (nameNameSpace name) $ "the exhaustiveness check for " ++ (occNameString $ nameOccName $ className cls)
        new_name = tidyNameOcc name occ_name
        ds_msg = TotalNonExhaustive (cxt {mc_fun = (L l new_name)}) flag maxPatterns vars nablas
    get_non_exhaustive_msg _ = Nothing
