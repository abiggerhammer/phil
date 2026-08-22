{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqExactReceive
  ( llvmExactReceiveCertificationSpec
  , knownExactReceiveRocqCertificationSpec
  ) where

import Data.Text (Text)
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

llvmExactReceiveCertificationSpec :: RocqCertificationSpec
llvmExactReceiveCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-exact-receive"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-EXACT-RECV-001"
  , rocqSpecClaim =
      "For a verified transport-exact-receive candidate, lowering preserves the exact Systems TransportHandle as the component-entry opaque pointer consumed by exact receive, the exact Begin.length U64 as the i64 length operand, and the exact Systems payload owner as the returned opaque payload handle; success is guarded by exact status == 1, EarlyEOF releases that exact returned owner, ordinary owner release preserves the same identity, ambient transport/payload recovery and evidence-derived runtime symbols are absent, and unauthorized pointer strengthening or identity drift rejects."
  , rocqSpecKind = "LLVM transport exact receive / payload ownership"
  , rocqSpecOrigin =
      "src/Phil/LLVM/ExactReceive.hs; src/Phil/LLVM/Lower.hs; src/Phil/LLVM/IR.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/ExactReceive.v"
  , rocqSpecScope = "Phil.LLVM transport-exact-receive-v1"
  , rocqSpecRepresentation = "normalized explicit transport/result/payload-owner target model"
  , rocqSpecSubjects =
      [ "TransportHandle"
      , "Begin.length U64"
      , "LLVMExactReceive"
      , "OwnedBuffer payload owner"
      , "EarlyEOF cleanup"
      ]
  , rocqSpecTheorems =
      [ "verified_exact_receive_reuses_recognized_record_authority"
      , "verified_exact_receive_reuses_runtime_symbol_authority"
      , "verified_exact_receive_preserves_explicit_transport"
      , "verified_exact_receive_preserves_begin_length_u64"
      , "verified_exact_receive_materializes_exact_payload_owner"
      , "verified_exact_receive_uses_fail_closed_status_and_exact_edges"
      , "verified_exact_receive_releases_exact_owner_on_failure_and_later_release"
      , "verified_exact_receive_forbids_ambient_state_layout_access_and_unauthorized_strengthening"
      , "exact_receive_transport_drift_is_rejected"
      , "exact_receive_length_drift_is_rejected"
      , "exact_receive_payload_identity_drift_is_rejected"
      , "exact_receive_status_drift_is_rejected"
      , "exact_receive_failure_cleanup_drift_is_rejected"
      , "exact_receive_ordinary_release_drift_is_rejected"
      , "exact_receive_ambient_state_is_rejected"
      , "exact_receive_payload_layout_or_strengthening_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/ExactReceive.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/ExactReceive.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-EXACT-RECV-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-EXACT-RECV-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness, reviewed correspondence from Phil.LLVM.ExactReceive/Lower/IR/Verify identities and rendered LLVM to the normalized proof model, runtime implementation of the opaque transport/payload ABI, target calling convention, and payload ownership representation remain explicit trust boundaries."
  }

knownExactReceiveRocqCertificationSpec :: Text -> Maybe RocqCertificationSpec
knownExactReceiveRocqCertificationSpec profile
  | profile == rocqSpecProfile llvmExactReceiveCertificationSpec =
      Just llvmExactReceiveCertificationSpec
  | otherwise = Nothing
