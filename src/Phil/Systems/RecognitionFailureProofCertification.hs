{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RecognitionFailureProofCertification
  ( systemsRecognitionFailureDetailCertificationSpec
  ) where

import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

systemsRecognitionFailureDetailCertificationSpec :: RocqCertificationSpec
systemsRecognitionFailureDetailCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-recognition-failure-detail"
  , rocqSpecObligation = ObligationId "PHIL-SYS-RECOG-FAIL-DETAIL-001"
  , rocqSpecClaim =
      "For the verified current Phase 0 StorageFailure successor, the merged RecognitionFailure semantic witness remains exact: Hello and Begin recognition gates retain their exact pending ingress, frame owner, RecognitionBoundary site and dedicated failure edge; each failure edge materializes one grammar-specific RuntimeOpaque recognition reason from the exact pending ingress, forwards that exact reason exactly once into the matching fatal recognition effect, destroys the exact pending/frame pair, and terminates in the exact grammar-specific RecognitionFailure class; the Hello and Begin reason identities remain distinct; success paths are unchanged; the recognition-failure-detail lowering decision is rebound to the current successor; certified ClientOutbound predecessor authority is preserved; and no concrete reason representation, runtime/diagnostic ABI, wire encoding, or outer framing is claimed."
  , rocqSpecKind = "Systems recognition failure reason identity and fatal flow"
  , rocqSpecOrigin =
      "src/Phil/Systems/RecognitionFailure.hs; src/Phil/Systems/StorageFailure.hs; test/RecognitionFailureMain.hs; test/StorageFailureMain.hs; proof/Phil/Systems/RecognitionFailureDetail.v"
  , rocqSpecScope =
      "Phil.Systems current StorageFailure successor preserving Hello/Begin recognition rejected(reason) semantics"
  , rocqSpecRepresentation =
      "failure-only grammar-specific RuntimeOpaque recognition reason identities with exact pending provenance, fatal forwarding, pending/frame destruction, and terminal class"
  , rocqSpecSubjects =
      [ "UploadServer/server.entry -> server.hello.recognition_failure"
      , "server.pending.hello / server.frame.hello"
      , "server.hello_recognition_reason : RuntimeOpaque[RecognitionReason[Hello]]"
      , "fail recognition Hello(server.pending.hello, server.hello_recognition_reason)"
      , "UploadServer/server.version -> server.begin.recognition_failure"
      , "server.pending.begin / server.frame.begin"
      , "server.begin_recognition_reason : RuntimeOpaque[RecognitionReason[Begin]]"
      , "fail recognition Begin(server.pending.begin, server.begin_recognition_reason)"
      , "lower.recognition.failure_detail"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_recognition_failure_is_preserved_by_current_successor"
      , "verified_systems_recognition_failure_preserves_exact_hello_failure_flow"
      , "verified_systems_recognition_failure_preserves_exact_begin_failure_flow"
      , "verified_systems_recognition_failure_preserves_distinct_single_use_reasons"
      , "verified_systems_recognition_failure_binds_decision_and_claims_no_physical_representation"
      , "systems_recognition_failure_reason_or_provenance_drift_is_rejected"
      , "systems_recognition_failure_cleanup_or_terminal_drift_is_rejected"
      , "systems_recognition_failure_physical_claim_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/RecognitionFailureDetail.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/RecognitionFailureDetail.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-RECOG-FAIL-DETAIL-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-RECOG-FAIL-DETAIL-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell grammar/pending/frame/reason/block/site identities, operation order and multiplicity, exact reason-use enumeration, decision rebinding, and the current StorageFailure successor's explicit preservation of RecognitionFailure and ClientOutbound witnesses remain trust boundaries. Recognizer error-object contents/lifetime, physical reason representation, diagnostic/runtime ABI, concrete I/O, wire encoding, and outer framing are not proved."
  }
