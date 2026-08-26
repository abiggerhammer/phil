{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.EvidenceTransferWitnesses
  ( uploadEvidenceTransferWithoutRelation
  , steveEvidenceTransferWithoutRelation
  , steveCheckedCopyTransfer
  , uploadUncheckedRebinding
  , steveUncheckedRebinding
  , steveSyntheticCopyRelation
  , steveCheckedRebinding
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.SubjectWitnesses
  ( steveCandidateSubject
  , steveReadSubject
  , steveSubjectStageBundle
  , uploadClientPayloadSubject
  , uploadPayloadSubject
  , uploadSubjectStageBundle
  )
import Phil.Systems.EvidenceSubjectTransfer
import Phil.Systems.SubjectCorrespondence
  ( SubjectValidityScopeRevision (..)
  )

uploadEvidenceTransferWithoutRelation :: EvidenceTransferStageBundle
uploadEvidenceTransferWithoutRelation = makeEvidenceTransferStageBundle
  uploadSubjectStageBundle
  Map.empty
  (Map.singleton (evidenceRebindingKey uploadUncheckedRebinding) uploadUncheckedRebinding)

steveEvidenceTransferWithoutRelation :: Either String EvidenceTransferStageBundle
steveEvidenceTransferWithoutRelation = do
  base <- steveSubjectStageBundle
  pure (makeEvidenceTransferStageBundle
    base
    Map.empty
    (Map.singleton (evidenceRebindingKey steveUncheckedRebinding) steveUncheckedRebinding))

steveCheckedCopyTransfer :: Either String EvidenceTransferStageBundle
steveCheckedCopyTransfer = do
  base <- steveSubjectStageBundle
  pure (makeEvidenceTransferStageBundle
    base
    (Map.singleton
      (subjectTransferRelationKey steveSyntheticCopyRelation)
      steveSyntheticCopyRelation)
    (Map.singleton
      (evidenceRebindingKey steveCheckedRebinding)
      steveCheckedRebinding))

uploadUncheckedRebinding :: EvidenceRebindingClaim
uploadUncheckedRebinding = EvidenceRebindingClaim
  { evidenceRebindingKey = EvidenceRebindingKey "upload.payload-send-evidence.rebind-without-copy"
  , evidenceRebindingSource = uploadClientPayloadSubject
  , evidenceRebindingTarget = uploadPayloadSubject
  , evidenceRebindingEvidenceRefs = Set.singleton "payload.exact_send"
  , evidenceRebindingRelation = Nothing
  }

steveUncheckedRebinding :: EvidenceRebindingClaim
steveUncheckedRebinding = EvidenceRebindingClaim
  { evidenceRebindingKey = EvidenceRebindingKey "steve.borrow-evidence.rebind-without-copy"
  , evidenceRebindingSource = steveCandidateSubject
  , evidenceRebindingTarget = steveReadSubject
  , evidenceRebindingEvidenceRefs = Set.singleton "steve.blob.borrow-preservation"
  , evidenceRebindingRelation = Nothing
  }

steveSyntheticCopyRelation :: SubjectTransferRelation
steveSyntheticCopyRelation = SubjectTransferRelation
  { subjectTransferRelationKey = SubjectTransferRelationKey "test.steve.candidate-to-read.exact-copy"
  , subjectTransferSource = steveCandidateSubject
  , subjectTransferTarget = steveReadSubject
  , subjectTransferBasis = CheckedSubjectCopy
      (CopyRelationRevision "copy.test.steve.candidate-to-read.v1")
      (ByteEqualityRevision "bytes.equal.test.steve.candidate-to-read.v1")
      (EvidenceTransferLawRevision "evidence-transfer.test.steve.borrow-preservation.v1")
  , subjectTransferAllowedEvidence = Set.singleton "steve.blob.borrow-preservation"
  , subjectTransferValidityScope = SubjectValidityScopeRevision
      "scope.test.steve.synthetic-exact-copy.v1"
  }

steveCheckedRebinding :: EvidenceRebindingClaim
steveCheckedRebinding = EvidenceRebindingClaim
  { evidenceRebindingKey = EvidenceRebindingKey "test.steve.borrow-evidence.rebind-with-copy"
  , evidenceRebindingSource = steveCandidateSubject
  , evidenceRebindingTarget = steveReadSubject
  , evidenceRebindingEvidenceRefs = Set.singleton "steve.blob.borrow-preservation"
  , evidenceRebindingRelation = Just
      (subjectTransferRelationKey steveSyntheticCopyRelation)
  }
