{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.EvidenceFactAuthority
  ( EvidenceFactAuthorityBinding (..)
  , EvidenceFactAuthorityError (..)
  , handoffResolvedObligationWithEvidenceAuthority
  ) where

import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Handoff
  ( HandoffConfig
  , HandoffError
  , LedgerHandoff
  , handoffResolvedObligationWithEvidence
  )
import Phil.Assurance.Types
  ( AssuranceLedger (..)
  , EvidenceEntry (..)
  , EvidenceEntryId
  , ObligationRevision (..)
  , RevisionId
  , renderPropositionCanonical
  )
import Phil.Core.Decision
  ( AssumptionRef (..)
  , DecisionCertificate (..)
  , LinearBasis (..)
  , LinearCertificate (..)
  )
import Phil.Core.Discharge
  ( ObligationDisposition (..)
  , ResolvedObligation (..)
  , StaticDischarge (..)
  )
import Phil.Core.Syntax
  ( Name
  , Obligation (..)
  , ObligationId
  , Proposition
  )

-- | Architecture-owned authority binding for one local Core EvidenceFact.
-- The immutable evidence identity is not sufficient by itself: the binding
-- also names the semantic subjects and scope that the architecture says the
-- local fact denotes. The checker-retained certificate remains authoritative
-- for the proposition itself.
data EvidenceFactAuthorityBinding = EvidenceFactAuthorityBinding
  { authorityEvidenceEntryId :: EvidenceEntryId
  , authoritySubjectIds :: [Text]
  , authorityScope :: Text
  }
  deriving (Eq, Show)

data EvidenceFactAuthorityError
  = EvidenceFactAuthorityHandoffError HandoffError
  | MissingEvidenceFactAuthority ObligationId Name Int
  | MissingAuthorityEvidenceEntry ObligationId Name Int EvidenceEntryId
  | MissingAuthorityEvidenceRevision ObligationId Name Int EvidenceEntryId RevisionId
  | EvidenceFactAuthorityPropositionMismatch ObligationId Name Int Text Text
  | EvidenceFactAuthoritySubjectMismatch ObligationId Name Int [Text] [Text]
  | EvidenceFactAuthorityScopeMismatch ObligationId Name Int Text Text
  deriving (Eq, Show)

-- | Validate every certificate-used EvidenceFact against the immutable
-- assurance ledger before reusing the ordinary lossless handoff.
--
-- The retained DecisionCertificate is the exact object checked by Core, so the
-- proposition carried beside an EvidenceFact is the proposition identity that
-- participated in certificate checking. The architecture-owned authority
-- binding supplies semantic subject/scope identity, and the selected immutable
-- evidence revision must agree with all three before the existing handoff is
-- allowed to emit DependsOnEvidence.
handoffResolvedObligationWithEvidenceAuthority
  :: HandoffConfig
  -> Map.Map (Name, Int) EvidenceFactAuthorityBinding
  -> AssuranceLedger
  -> ResolvedObligation
  -> Either EvidenceFactAuthorityError [LedgerHandoff]
handoffResolvedObligationWithEvidenceAuthority config authorities ledger root = do
  mapM_ validateUsedFact (usedEvidenceFacts root)
  mapLeft EvidenceFactAuthorityHandoffError $
    handoffResolvedObligationWithEvidence config evidenceIds root
  where
    evidenceIds = Map.map authorityEvidenceEntryId authorities

    validateUsedFact (consumer, name, index, proposition) = do
      authority <-
        case Map.lookup (name, index) authorities of
          Just binding -> Right binding
          Nothing -> Left (MissingEvidenceFactAuthority consumer name index)
      evidence <-
        case Map.lookup (authorityEvidenceEntryId authority) (ledgerEvidence ledger) of
          Just entry -> Right entry
          Nothing -> Left
            (MissingAuthorityEvidenceEntry
              consumer name index (authorityEvidenceEntryId authority))
      revision <-
        case Map.lookup (evidenceObligationRevision evidence) (ledgerRevisions ledger) of
          Just entry -> Right entry
          Nothing -> Left
            (MissingAuthorityEvidenceRevision
              consumer
              name
              index
              (authorityEvidenceEntryId authority)
              (evidenceObligationRevision evidence))
      let expectedStatement = renderPropositionCanonical proposition
          actualStatement = revisionStatement revision
      if actualStatement == expectedStatement
        then Right ()
        else Left
          (EvidenceFactAuthorityPropositionMismatch
            consumer name index expectedStatement actualStatement)
      let expectedSubjects = sort (authoritySubjectIds authority)
          actualSubjects = sort (revisionSubjectIds revision)
      if actualSubjects == expectedSubjects
        then Right ()
        else Left
          (EvidenceFactAuthoritySubjectMismatch
            consumer name index expectedSubjects actualSubjects)
      let expectedScope = authorityScope authority
          actualScope = revisionScope revision
      if actualScope == expectedScope
        then Right ()
        else Left
          (EvidenceFactAuthorityScopeMismatch
            consumer name index expectedScope actualScope)

usedEvidenceFacts :: ResolvedObligation -> [(ObligationId, Name, Int, Proposition)]
usedEvidenceFacts resolved =
  dispositionFacts <> concatMap usedEvidenceFacts (resolvedPrerequisites resolved)
  where
    consumer = obligationId (resolvedObligation resolved)
    dispositionFacts =
      case resolvedDisposition resolved of
        StaticallyDischarged StaticByCertificate { staticCertificate = certificate } ->
          [ (consumer, name, index, proposition)
          | (name, index, proposition) <- certificateEvidenceFacts certificate
          ]
        _ -> []

certificateEvidenceFacts :: DecisionCertificate -> [(Name, Int, Proposition)]
certificateEvidenceFacts certificate =
  case certificate of
    CertificateTruth -> []
    CertificateAssumption assumption proposition ->
      assumptionEvidenceFact assumption proposition
    CertificateLinear linear -> linearEvidenceFacts linear
    CertificateConjunction left right ->
      certificateEvidenceFacts left <> certificateEvidenceFacts right
    CertificateDisjunctionLeft left -> certificateEvidenceFacts left
    CertificateDisjunctionRight right -> certificateEvidenceFacts right
    CertificateNotEqualLeft linear -> linearEvidenceFacts linear
    CertificateNotEqualRight linear -> linearEvidenceFacts linear

linearEvidenceFacts :: LinearCertificate -> [(Name, Int, Proposition)]
linearEvidenceFacts linear = concat
  [ basisEvidenceFacts basis
  | (basis, _) <- linearTerms linear
  ]

basisEvidenceFacts :: LinearBasis -> [(Name, Int, Proposition)]
basisEvidenceFacts basis =
  case basis of
    BasisAssumption assumption proposition ->
      assumptionEvidenceFact assumption proposition
    BasisNatLower _ -> []
    BasisUIntLower _ _ -> []
    BasisUIntUpper _ _ -> []

assumptionEvidenceFact
  :: AssumptionRef
  -> Proposition
  -> [(Name, Int, Proposition)]
assumptionEvidenceFact assumption proposition =
  case assumption of
    EvidenceFact name index -> [(name, index, proposition)]
    PrerequisiteFact _ -> []

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
