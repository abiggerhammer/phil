{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.EvidenceErasureWitnesses
  ( uploadErasureAfterDischarge
  , uploadErasureWithoutDischarge
  , steveErasureAfterDischarge
  , steveErasureWithoutDischarge
  , uploadErasureKey
  , steveErasureKey
  , uploadErasureJustification
  , steveErasureJustification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.SubjectWitnesses
  ( steveCandidateSubject
  , steveSubjectStageBundle
  , uploadPayloadSubject
  , uploadSubjectStageBundle
  )
import Phil.Systems.EvidenceErasure
import Phil.Systems.EvidenceSubjectTransfer
  ( EvidenceTransferStageBundle
  , makeEvidenceTransferStageBundle
  )
import Phil.Systems.Phase1Stage
  ( SourceFactKey (..)
  )

uploadErasureKey, steveErasureKey :: ErasureJustificationKey
uploadErasureKey = ErasureJustificationKey "upload.payload.receive-proof.erasure"
steveErasureKey = ErasureJustificationKey "steve.digest.stable-subject-proof.erasure"

uploadErasureAfterDischarge :: EvidenceErasureStageBundle
uploadErasureAfterDischarge = makeEvidenceErasureStageBundle
  uploadEvidenceTransferBase
  (Map.singleton uploadErasureKey uploadErasureJustification)
  Map.empty

uploadErasureWithoutDischarge :: EvidenceErasureStageBundle
uploadErasureWithoutDischarge = makeEvidenceErasureStageBundle
  uploadEvidenceTransferBase
  (Map.singleton uploadErasureKey
    uploadErasureJustification { erasureDischargeEvidenceRefs = Set.empty })
  Map.empty

steveErasureAfterDischarge :: Either String EvidenceErasureStageBundle
steveErasureAfterDischarge = do
  base <- steveEvidenceTransferBase
  pure (makeEvidenceErasureStageBundle
    base
    (Map.singleton steveErasureKey steveErasureJustification)
    Map.empty)

steveErasureWithoutDischarge :: Either String EvidenceErasureStageBundle
steveErasureWithoutDischarge = do
  base <- steveEvidenceTransferBase
  pure (makeEvidenceErasureStageBundle
    base
    (Map.singleton steveErasureKey
      steveErasureJustification { erasureDischargeEvidenceRefs = Set.empty })
    Map.empty)

uploadErasureJustification :: ErasureJustification
uploadErasureJustification = ErasureJustification
  { erasureJustificationKey = uploadErasureKey
  , erasureSourceFact = SourceFactKey "payload.exact_receive"
  , erasureSubject = uploadPayloadSubject
  , erasureRepresentation = ErasedRepresentationKey
      "upload.payload.receive-validation-marker"
  , erasureDischargeEvidenceRefs = Set.singleton "payload.exact_receive"
  , erasureLastSemanticUse = SemanticUseKey
      "upload.server.payload.exact-receive-commit"
  , erasureSuccessorInvariant = Nothing
  , erasureNoLaterConsumerBasis = NoLaterConsumerRevision
      "consumer-closure.upload.payload.receive-proof.v1"
  , erasureRuntimeResidueChange = Just
      (RuntimeResidueChangeRevision "runtime-residue.upload.receive-proof.erased.v1")
  , erasureCostChange = Just
      (ErasureCostChangeRevision "cost.upload.receive-proof.erased.v1")
  }

steveErasureJustification :: ErasureJustification
steveErasureJustification = ErasureJustification
  { erasureJustificationKey = steveErasureKey
  , erasureSourceFact = SourceFactKey "steve.digest.stable-subject"
  , erasureSubject = steveCandidateSubject
  , erasureRepresentation = ErasedRepresentationKey
      "steve.digest.stable-subject-proof-marker"
  , erasureDischargeEvidenceRefs = Set.singleton "steve.digest.stable-subject"
  , erasureLastSemanticUse = SemanticUseKey
      "steve.put.digest-compute-semantic-use"
  , erasureSuccessorInvariant = Nothing
  , erasureNoLaterConsumerBasis = NoLaterConsumerRevision
      "consumer-closure.steve.digest.stable-subject.v1"
  , erasureRuntimeResidueChange = Just
      (RuntimeResidueChangeRevision "runtime-residue.steve.digest-proof.erased.v1")
  , erasureCostChange = Just
      (ErasureCostChangeRevision "cost.steve.digest-proof.erased.v1")
  }

uploadEvidenceTransferBase :: EvidenceTransferStageBundle
uploadEvidenceTransferBase = makeEvidenceTransferStageBundle
  uploadSubjectStageBundle
  Map.empty
  Map.empty

steveEvidenceTransferBase :: Either String EvidenceTransferStageBundle
steveEvidenceTransferBase = do
  subjectBase <- steveSubjectStageBundle
  pure (makeEvidenceTransferStageBundle subjectBase Map.empty Map.empty)
