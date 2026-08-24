{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.StorageFailureProofCertification
  ( systemsStorageFailureDetailCertificationSpec
  ) where

import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

systemsStorageFailureDetailCertificationSpec :: RocqCertificationSpec
systemsStorageFailureDetailCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-storage-failure-detail"
  , rocqSpecObligation = ObligationId "PHIL-SYS-STORAGE-FAIL-DETAIL-001"
  , rocqSpecClaim =
      "For the verified current Phase 0 StorageFailure successor, the already-established recognition-failure and client-outbound semantic witnesses remain preserved; the exact server.transport, server.payload owner, server.upload_id result, retained StorageBoundary site, and original success/failure continuations are preserved; storage retains consume-on-all-outcomes ownership semantics; the failure-only server.storage_error : RuntimeOpaque[StorageError] is materialized exactly once with no semantic input, forwarded exactly once with the exact server transport into fail internal storage, and terminates as StorageFailure; server.payload has no post-transfer semantic use and no new owner or alias is introduced; lower.storage.failure_detail is rebound to the exact current successor; and no concrete error representation, broadened storage ABI, wire encoding, or outer framing is claimed."
  , rocqSpecKind = "Systems storage failure detail and post-transfer ownership boundary"
  , rocqSpecOrigin =
      "src/Phil/Systems/StorageFailure.hs; docs/phase-0/storage-failure-detail-v1.md; test/StorageFailureMain.hs; proof/Phil/Systems/StorageFailureDetail.v"
  , rocqSpecScope =
      "Phil.Systems final StorageFailure successor preserving storage error identity after ownership transfer"
  , rocqSpecRepresentation =
      "TermStore consume-on-all-outcomes plus failure-only RuntimeOpaque[StorageError] materialization and exact fatal forwarding"
  , rocqSpecSubjects =
      [ "UploadServer/server.store"
      , "UploadServer/server.storage_failure"
      , "server.transport : TransportHandle"
      , "server.payload : OwnedBuffer[Bytes[begin.length]]"
      , "server.upload_id : RuntimeScalar[UploadId]"
      , "server.storage_error : RuntimeOpaque[StorageError]"
      , "materialize storage failure error"
      , "fail internal storage"
      , "StorageFailure"
      , "lower.storage.failure_detail"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_storage_failure_is_current_successor"
      , "verified_systems_storage_failure_preserves_predecessor_authority"
      , "verified_systems_storage_failure_preserves_store_transfer_boundary"
      , "verified_systems_storage_failure_preserves_exact_error_flow"
      , "verified_systems_storage_failure_preserves_no_post_transfer_payload_use"
      , "verified_systems_storage_failure_binds_decision_and_claims_no_physical_error_abi"
      , "systems_storage_failure_error_flow_drift_is_rejected"
      , "systems_storage_failure_post_transfer_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/StorageFailureDetail.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/StorageFailureDetail.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-STORAGE-FAIL-DETAIL-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-STORAGE-FAIL-DETAIL-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell ValueId/BlockId/RuntimeSiteRef identities, exact TermStore ownership/result/continuation identities, operation multiplicity, semantic-use enumeration, lowering-decision rebinding, and current predecessor-witness preservation remain explicit trust boundaries. The pending PHIL-SYS-RECOG-FAIL-DETAIL-001 proof is the semantic predecessor authority in the ledger but is not imported as if already discharged. Concrete StorageError layout/lifetime, provider failure object semantics, revised physical storage ABI, fatal diagnostic behavior, physical I/O, and outer framing are not proved."
  }
