{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.DataSubjectTransport
  ( DataSubject (..)
  , SubjectBoundEvidence (..)
  , DataSubjectUpdate (..)
  , DataSubjectTransportKind (..)
  , DataSubjectTransportDisposition (..)
  , DataSubjectTransport (..)
  , CheckedDataSubjectUpdate (..)
  , DataSubjectTransportError (..)
  , subjectEvidenceProposition
  , checkDataSubjectEvidenceUpdate
  ) where

import qualified DataSubjectKernel as Kernel
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Refinement
  ( normalizeProposition
  , propositionMentions
  , substituteProposition
  )
import Phil.Core.Syntax
  ( Name
  , Proposition
  , RefSort (..)
  , RefTerm (..)
  )

data DataSubject = DataSubject
  { dataSubjectIdentity :: RefTerm
  , dataSubjectRepresentationToken :: Maybe Text
  }
  deriving (Eq, Ord, Show)

data SubjectBoundEvidence = SubjectBoundEvidence
  { subjectEvidenceReference :: Text
  , subjectEvidenceBinder :: Name
  , subjectEvidenceTemplate :: Proposition
  , subjectEvidenceSubject :: DataSubject
  }
  deriving (Eq, Ord, Show)

data DataSubjectUpdate = DataSubjectUpdate
  { dataSubjectUpdatePrior :: DataSubject
  , dataSubjectUpdateReplacement :: DataSubject
  , dataSubjectUpdatePriorConsumed :: Bool
  , dataSubjectUpdateReplacementConstructed :: Bool
  }
  deriving (Eq, Ord, Show)

data DataSubjectTransportKind
  = SubjectCopyTransport
  | SubjectSuccessionTransport
  deriving (Eq, Ord, Show)

data DataSubjectTransportDisposition
  = SubjectTransportAccepted
  | SubjectTransportRejected Text
  deriving (Eq, Ord, Show)

data DataSubjectTransport = DataSubjectTransport
  { dataSubjectTransportKind :: DataSubjectTransportKind
  , dataSubjectTransportRelationRevision :: Text
  , dataSubjectTransportEvidenceReference :: Text
  , dataSubjectTransportPriorIdentity :: RefTerm
  , dataSubjectTransportReplacementIdentity :: RefTerm
  , dataSubjectTransportSourceProposition :: Proposition
  , dataSubjectTransportTargetProposition :: Proposition
  , dataSubjectTransportDisposition :: DataSubjectTransportDisposition
  }
  deriving (Eq, Ord, Show)

data CheckedDataSubjectUpdate = CheckedDataSubjectUpdate
  { checkedDataSubjectPrior :: DataSubject
  , checkedDataSubjectReplacement :: DataSubject
  , checkedDataSubjectSourceEvidence :: SubjectBoundEvidence
  , checkedDataSubjectResultEvidence :: SubjectBoundEvidence
  , checkedDataSubjectTransport :: Maybe DataSubjectTransport
  }
  deriving (Eq, Ord, Show)

data DataSubjectTransportError
  = DataSubjectPriorNotConsumed
  | DataSubjectReplacementNotConstructed
  | DataSubjectNotStableIdentity RefTerm
  | DataSubjectKindMismatch Text Text
  | DataSubjectEvidenceTemplateDoesNotMentionSubject Name
  | DataSubjectEvidencePriorMismatch RefTerm RefTerm
  | DataSubjectUnexpectedTransportForSameSubject
  | DataSubjectTransportRequired RefTerm RefTerm
  | DataSubjectTransportRejected Text
  | DataSubjectTransportRelationRevisionMissing
  | DataSubjectTransportEvidenceMismatch Text Text
  | DataSubjectTransportPriorMismatch RefTerm RefTerm
  | DataSubjectTransportReplacementMismatch RefTerm RefTerm
  | DataSubjectTransportSourcePropositionMismatch Proposition Proposition
  | DataSubjectTransportTargetPropositionMismatch Proposition Proposition
  deriving (Eq, Ord, Show)

subjectEvidenceProposition :: SubjectBoundEvidence -> Proposition
subjectEvidenceProposition evidence = normalizeProposition $
  substituteProposition
    (subjectEvidenceBinder evidence)
    (dataSubjectIdentity (subjectEvidenceSubject evidence))
    (subjectEvidenceTemplate evidence)

checkDataSubjectEvidenceUpdate
  :: DataSubjectUpdate
  -> SubjectBoundEvidence
  -> Maybe DataSubjectTransport
  -> Either DataSubjectTransportError CheckedDataSubjectUpdate
checkDataSubjectEvidenceUpdate update evidence maybeTransport = do
  let prior = dataSubjectUpdatePrior update
      replacement = dataSubjectUpdateReplacement update
      priorIdentity = dataSubjectIdentity prior
      replacementIdentity = dataSubjectIdentity replacement
      evidenceIdentity = dataSubjectIdentity (subjectEvidenceSubject evidence)
      priorKindResult = stableIdentityKind priorIdentity
      replacementKindResult = stableIdentityKind replacementIdentity
      evidenceKindResult = stableIdentityKind evidenceIdentity
      priorStable = stableResult priorKindResult
      replacementStable = stableResult replacementKindResult
      evidenceStable = stableResult evidenceKindResult
      kindsMatch = stableKindsMatch priorKindResult replacementKindResult
      evidenceKindMatchesPrior = stableKindsMatch priorKindResult evidenceKindResult
      evidenceTemplateMentionsSubject =
        propositionMentions
          (subjectEvidenceBinder evidence)
          (subjectEvidenceTemplate evidence)
      evidenceMatchesPrior = evidenceIdentity == priorIdentity

  case Kernel.decideDataSubjectPrerequisites
      (dataSubjectUpdatePriorConsumed update)
      (dataSubjectUpdateReplacementConstructed update)
      priorStable
      replacementStable
      kindsMatch
      evidenceTemplateMentionsSubject
      evidenceMatchesPrior
      evidenceStable
      evidenceKindMatchesPrior of
    Kernel.DataSubjectPrerequisitesAccepted -> Right ()
    Kernel.DataSubjectPriorNotConsumedDecision ->
      Left DataSubjectPriorNotConsumed
    Kernel.DataSubjectReplacementNotConstructedDecision ->
      Left DataSubjectReplacementNotConstructed
    Kernel.DataSubjectPriorNotStableDecision ->
      Left (stableFailure priorIdentity priorKindResult)
    Kernel.DataSubjectReplacementNotStableDecision ->
      Left (stableFailure replacementIdentity replacementKindResult)
    Kernel.DataSubjectKindMismatchDecision ->
      Left (kindMismatchFailure priorIdentity replacementIdentity
        priorKindResult replacementKindResult)
    Kernel.DataSubjectEvidenceTemplateMissingSubjectDecision ->
      Left (DataSubjectEvidenceTemplateDoesNotMentionSubject
        (subjectEvidenceBinder evidence))
    Kernel.DataSubjectEvidencePriorMismatchDecision ->
      Left (DataSubjectEvidencePriorMismatch priorIdentity evidenceIdentity)
    Kernel.DataSubjectEvidenceNotStableDecision ->
      Left (stableFailure evidenceIdentity evidenceKindResult)
    Kernel.DataSubjectEvidenceKindMismatchDecision ->
      Left (kindMismatchFailure priorIdentity evidenceIdentity
        priorKindResult evidenceKindResult)

  let resultEvidence = evidence { subjectEvidenceSubject = replacement }
      sourceProposition = subjectEvidenceProposition evidence
      targetProposition = subjectEvidenceProposition resultEvidence
      sameSubject = priorIdentity == replacementIdentity
      transportPresent = case maybeTransport of
        Nothing -> False
        Just _ -> True

  case Kernel.decideDataSubjectTransportMode sameSubject transportPresent of
    Kernel.DataSubjectUnexpectedTransportDecision ->
      Left DataSubjectUnexpectedTransportForSameSubject
    Kernel.DataSubjectTransportRequiredDecision ->
      Left (DataSubjectTransportRequired priorIdentity replacementIdentity)
    Kernel.DataSubjectTransportModeAccepted -> case maybeTransport of
      Nothing -> Right CheckedDataSubjectUpdate
        { checkedDataSubjectPrior = prior
        , checkedDataSubjectReplacement = replacement
        , checkedDataSubjectSourceEvidence = evidence
        , checkedDataSubjectResultEvidence = resultEvidence
        , checkedDataSubjectTransport = Nothing
        }
      Just transport -> do
        validateTransport
          priorIdentity replacementIdentity sourceProposition targetProposition
          evidence transport
        Right CheckedDataSubjectUpdate
          { checkedDataSubjectPrior = prior
          , checkedDataSubjectReplacement = replacement
          , checkedDataSubjectSourceEvidence = evidence
          , checkedDataSubjectResultEvidence = resultEvidence
          , checkedDataSubjectTransport = Just transport
          }

validateTransport
  :: RefTerm
  -> RefTerm
  -> Proposition
  -> Proposition
  -> SubjectBoundEvidence
  -> DataSubjectTransport
  -> Either DataSubjectTransportError ()
validateTransport priorIdentity replacementIdentity sourceProposition targetProposition evidence transport =
  case Kernel.decideDataSubjectTransport
      dispositionAccepted
      revisionNonempty
      evidenceReferenceMatches
      priorIdentityMatches
      replacementIdentityMatches
      sourcePropositionMatches
      targetPropositionMatches of
    Kernel.DataSubjectTransportAcceptedDecision -> Right ()
    Kernel.DataSubjectTransportDispositionRejectedDecision ->
      Left dispositionFailure
    Kernel.DataSubjectTransportRevisionMissingDecision ->
      Left DataSubjectTransportRelationRevisionMissing
    Kernel.DataSubjectTransportEvidenceMismatchDecision ->
      Left (DataSubjectTransportEvidenceMismatch expectedReference actualReference)
    Kernel.DataSubjectTransportPriorMismatchDecision ->
      Left (DataSubjectTransportPriorMismatch priorIdentity actualPrior)
    Kernel.DataSubjectTransportReplacementMismatchDecision ->
      Left (DataSubjectTransportReplacementMismatch
        replacementIdentity actualReplacement)
    Kernel.DataSubjectTransportSourcePropositionMismatchDecision ->
      Left (DataSubjectTransportSourcePropositionMismatch
        sourceProposition actualSource)
    Kernel.DataSubjectTransportTargetPropositionMismatchDecision ->
      Left (DataSubjectTransportTargetPropositionMismatch
        targetProposition actualTarget)
  where
    (dispositionAccepted, dispositionFailure) =
      case dataSubjectTransportDisposition transport of
        SubjectTransportAccepted ->
          (True, DataSubjectTransportRejected
            "internal data subject disposition reflection mismatch")
        SubjectTransportRejected reason ->
          (False, DataSubjectTransportRejected reason)
    revisionNonempty = not (Text.null (dataSubjectTransportRelationRevision transport))
    expectedReference = subjectEvidenceReference evidence
    actualReference = dataSubjectTransportEvidenceReference transport
    evidenceReferenceMatches = actualReference == expectedReference
    actualPrior = dataSubjectTransportPriorIdentity transport
    priorIdentityMatches = actualPrior == priorIdentity
    actualReplacement = dataSubjectTransportReplacementIdentity transport
    replacementIdentityMatches = actualReplacement == replacementIdentity
    actualSource = normalizeProposition (dataSubjectTransportSourceProposition transport)
    sourcePropositionMatches = actualSource == sourceProposition
    actualTarget = normalizeProposition (dataSubjectTransportTargetProposition transport)
    targetPropositionMatches = actualTarget == targetProposition

stableResult :: Either DataSubjectTransportError Text -> Bool
stableResult result = case result of
  Right _ -> True
  Left _ -> False

stableKindsMatch
  :: Either DataSubjectTransportError Text
  -> Either DataSubjectTransportError Text
  -> Bool
stableKindsMatch left right = case (left, right) of
  (Right leftKind, Right rightKind) -> leftKind == rightKind
  _ -> False

stableFailure
  :: RefTerm
  -> Either DataSubjectTransportError Text
  -> DataSubjectTransportError
stableFailure identity result = case result of
  Left err -> err
  Right _ -> DataSubjectNotStableIdentity identity

kindMismatchFailure
  :: RefTerm
  -> RefTerm
  -> Either DataSubjectTransportError Text
  -> Either DataSubjectTransportError Text
  -> DataSubjectTransportError
kindMismatchFailure leftIdentity rightIdentity left right = case (left, right) of
  (Right leftKind, Right rightKind) -> DataSubjectKindMismatch leftKind rightKind
  (Left err, _) -> err
  (_, Left err) -> err
  _ -> DataSubjectKindMismatch
    (representationFallback leftIdentity)
    (representationFallback rightIdentity)

representationFallback :: RefTerm -> Text
representationFallback _ = "internal data subject kind reflection mismatch"

stableIdentityKind :: RefTerm -> Either DataSubjectTransportError Text
stableIdentityKind identity = case identity of
  RefOpaque (SortStableId kind) _ -> Right kind
  RefField _ _ (SortStableId kind) -> Right kind
  _ -> Left (DataSubjectNotStableIdentity identity)
