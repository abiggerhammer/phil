{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.EvidenceLineage
  ( ProofDischargeTargetIdentity (..)
  , ProofEvidenceLineage (..)
  , deriveProofDischargeTargetIdentity
  , deriveProofEvidenceLineage
  ) where

import Data.Text (Text)
import Phil.Assurance.Types (Digest, RevisionId)
import Phil.Core.Decision (DecisionCertificate)
import Phil.Verification.ProofEvidence
  ( CheckedProofEvidence
  , checkedProofCertificate
  , checkedProofChecker
  , checkedProofContextIds
  , checkedProofEvidenceFormat
  , checkedProofGraphRevision
  , checkedProofObligationRevision
  , checkedProofProducer
  , checkedProofSubjectIds
  )

-- | Semantic identity of the exact discharge target.  Accepted proof artifacts
-- do not participate in this identity: changing producer or certificate lineage
-- cannot retarget or re-key the already-fixed application obligation.
data ProofDischargeTargetIdentity = ProofDischargeTargetIdentity
  { proofDischargeGraphRevision :: Digest
  , proofDischargeObligationRevision :: RevisionId
  }
  deriving (Eq, Ord, Show)

-- | Evidence/assurance lineage for one competent proof path.  This records the
-- replaceable producer and accepted artifact details separately from the exact
-- semantic target identity.
data ProofEvidenceLineage = ProofEvidenceLineage
  { proofEvidenceLineageTarget :: ProofDischargeTargetIdentity
  , proofEvidenceLineageProducer :: Text
  , proofEvidenceLineageChecker :: Text
  , proofEvidenceLineageFormat :: Text
  , proofEvidenceLineageSubjects :: [Text]
  , proofEvidenceLineageContexts :: [Text]
  , proofEvidenceLineageCertificate :: DecisionCertificate
  }
  deriving (Eq, Ord, Show)

deriveProofDischargeTargetIdentity
  :: CheckedProofEvidence
  -> ProofDischargeTargetIdentity
deriveProofDischargeTargetIdentity checked = ProofDischargeTargetIdentity
  { proofDischargeGraphRevision = checkedProofGraphRevision checked
  , proofDischargeObligationRevision = checkedProofObligationRevision checked
  }

deriveProofEvidenceLineage
  :: CheckedProofEvidence
  -> ProofEvidenceLineage
deriveProofEvidenceLineage checked = ProofEvidenceLineage
  { proofEvidenceLineageTarget = deriveProofDischargeTargetIdentity checked
  , proofEvidenceLineageProducer = checkedProofProducer checked
  , proofEvidenceLineageChecker = checkedProofChecker checked
  , proofEvidenceLineageFormat = checkedProofEvidenceFormat checked
  , proofEvidenceLineageSubjects = checkedProofSubjectIds checked
  , proofEvidenceLineageContexts = checkedProofContextIds checked
  , proofEvidenceLineageCertificate = checkedProofCertificate checked
  }
