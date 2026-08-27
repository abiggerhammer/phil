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

-- | A stable semantic subject. Representation metadata is deliberately carried
-- beside, rather than inside, the semantic identity so pointer/handle/token
-- coincidence cannot establish subject equality.
data DataSubject = DataSubject
  { dataSubjectIdentity :: RefTerm
  , dataSubjectRepresentationToken :: Maybe Text
  }
  deriving (Eq, Ord, Show)

-- | Evidence represented as a proposition template with one distinguished
-- stable-subject binder. Instantiating that binder is the only operation in
-- this module that changes which semantic subject the evidence talks about.
data SubjectBoundEvidence = SubjectBoundEvidence
  { subjectEvidenceReference :: Text
  , subjectEvidenceBinder :: Name
  , subjectEvidenceTemplate :: Proposition
  , subjectEvidenceSubject :: DataSubject
  }
  deriving (Eq, Ord, Show)

-- | A consume-and-reconstruct update. Both facts must be explicit before any
-- subject-preservation or subject-succession reasoning is attempted.
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

-- | Explicit justification for moving one exact evidence item from one exact
-- stable semantic subject to another. The source/target propositions are
-- recorded explicitly so a transport cannot silently rewrite a different
-- proposition just because the two subjects share a type or representation.
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
  if dataSubjectUpdatePriorConsumed update
    then Right ()
    else Left DataSubjectPriorNotConsumed
  if dataSubjectUpdateReplacementConstructed update
    then Right ()
    else Left DataSubjectReplacementNotConstructed

  let prior = dataSubjectUpdatePrior update
      replacement = dataSubjectUpdateReplacement update
      priorIdentity = dataSubjectIdentity prior
      replacementIdentity = dataSubjectIdentity replacement
      evidenceIdentity = dataSubjectIdentity (subjectEvidenceSubject evidence)

  priorKind <- stableIdentityKind priorIdentity
  replacementKind <- stableIdentityKind replacementIdentity
  if priorKind == replacementKind
    then Right ()
    else Left (DataSubjectKindMismatch priorKind replacementKind)

  if propositionMentions (subjectEvidenceBinder evidence) (subjectEvidenceTemplate evidence)
    then Right ()
    else Left (DataSubjectEvidenceTemplateDoesNotMentionSubject
      (subjectEvidenceBinder evidence))

  if evidenceIdentity == priorIdentity
    then Right ()
    else Left (DataSubjectEvidencePriorMismatch priorIdentity evidenceIdentity)

  let resultEvidence = evidence { subjectEvidenceSubject = replacement }
      sourceProposition = subjectEvidenceProposition evidence
      targetProposition = subjectEvidenceProposition resultEvidence

  if priorIdentity == replacementIdentity
    then case maybeTransport of
      Nothing -> Right CheckedDataSubjectUpdate
        { checkedDataSubjectPrior = prior
        , checkedDataSubjectReplacement = replacement
        , checkedDataSubjectSourceEvidence = evidence
        , checkedDataSubjectResultEvidence = resultEvidence
        , checkedDataSubjectTransport = Nothing
        }
      Just _ -> Left DataSubjectUnexpectedTransportForSameSubject
    else case maybeTransport of
      Nothing -> Left (DataSubjectTransportRequired priorIdentity replacementIdentity)
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
validateTransport priorIdentity replacementIdentity sourceProposition targetProposition evidence transport = do
  case dataSubjectTransportDisposition transport of
    SubjectTransportAccepted -> Right ()
    SubjectTransportRejected reason -> Left (DataSubjectTransportRejected reason)

  if Text.null (dataSubjectTransportRelationRevision transport)
    then Left DataSubjectTransportRelationRevisionMissing
    else Right ()

  let expectedReference = subjectEvidenceReference evidence
      actualReference = dataSubjectTransportEvidenceReference transport
  if actualReference == expectedReference
    then Right ()
    else Left (DataSubjectTransportEvidenceMismatch expectedReference actualReference)

  let actualPrior = dataSubjectTransportPriorIdentity transport
  if actualPrior == priorIdentity
    then Right ()
    else Left (DataSubjectTransportPriorMismatch priorIdentity actualPrior)

  let actualReplacement = dataSubjectTransportReplacementIdentity transport
  if actualReplacement == replacementIdentity
    then Right ()
    else Left (DataSubjectTransportReplacementMismatch
      replacementIdentity actualReplacement)

  let actualSource = normalizeProposition (dataSubjectTransportSourceProposition transport)
  if actualSource == sourceProposition
    then Right ()
    else Left (DataSubjectTransportSourcePropositionMismatch
      sourceProposition actualSource)

  let actualTarget = normalizeProposition (dataSubjectTransportTargetProposition transport)
  if actualTarget == targetProposition
    then Right ()
    else Left (DataSubjectTransportTargetPropositionMismatch
      targetProposition actualTarget)

stableIdentityKind :: RefTerm -> Either DataSubjectTransportError Text
stableIdentityKind identity = case identity of
  RefOpaque (SortStableId kind) _ -> Right kind
  RefField _ _ (SortStableId kind) -> Right kind
  _ -> Left (DataSubjectNotStableIdentity identity)
