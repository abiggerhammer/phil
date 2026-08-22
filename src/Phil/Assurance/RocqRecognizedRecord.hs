{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqRecognizedRecord
  ( systemsRecognizedRecordCertificationSpec
  , llvmRecognizedRecordABICertificationSpec
  , llvmRuntimeSymbolCertificationSpec
  , knownRecognizedRecordRocqCertificationSpec
  ) where

import Data.Text (Text)
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

systemsRecognizedRecordCertificationSpec :: RocqCertificationSpec
systemsRecognizedRecordCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-recognized-record"
  , rocqSpecObligation = ObligationId "PHIL-SYS-RECORD-001"
  , rocqSpecClaim =
      "A verified recognized-record candidate ties an explicit RuntimeRecord value to the matching pending-ingress grammar and recognition-success path; commit precedes exactly one record materialization, which precedes exactly one schema-typed field projection consuming that exact record; the projection's exact scalar feeds the intended exact-receive consumer, and both content-bound lowering decisions must match."
  , rocqSpecKind = "Systems recognized-record provenance"
  , rocqSpecOrigin =
      "src/Phil/Systems/RecognizedRecord.hs; proof/Phil/Systems/RecognizedRecord.v"
  , rocqSpecScope = "Phil.Systems.RecognizedRecord"
  , rocqSpecRepresentation = "normalized recognition/provenance/dataflow model"
  , rocqSpecSubjects =
      [ "RuntimeRecord Begin"
      , "recognized Begin.length"
      , "TermReceiveExact"
      ]
  , rocqSpecTheorems =
      [ "verified_recognized_record_preserves_recognition_provenance"
      , "verified_recognized_record_materializes_once_after_commit"
      , "verified_recognized_record_projection_consumes_exact_record"
      , "verified_recognized_record_preserves_schema_type_and_exact_receive"
      , "verified_recognized_record_decisions_are_exact"
      , "verified_recognized_record_output_has_unique_preceding_definition"
      , "recognized_record_wrong_record_identity_is_rejected"
      , "recognized_record_competing_materialization_is_rejected"
      , "recognized_record_bad_ordering_is_rejected"
      , "recognized_record_schema_or_type_drift_is_rejected"
      , "recognized_record_exact_receive_drift_is_rejected"
      , "recognized_record_decision_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/RecognizedRecord.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/RecognizedRecord.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-RECORD-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-RECORD-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus correspondence from concrete Haskell Text/ValueId/BlockId identities, Data.Map/list enumeration, schema lookup, operation indexing, and the concrete Systems candidate to the normalized model remain explicit trust boundaries."
  }

llvmRecognizedRecordABICertificationSpec :: RocqCertificationSpec
llvmRecognizedRecordABICertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-recognized-record-abi"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-REC-ABI-001"
  , rocqSpecClaim =
      "For the recognized-record ABI v1 target, verified lowering maps the matching recognition site to one { i8, ptr } runtime result, branches on status == 1, binds the record SSA handle from that same result, projects Begin.length through the exact typed accessor on that handle, and passes the exact projected U64 SSA value to receive_exact_u64; record-layout access and pointer-strengthening not separately authorized must not appear."
  , rocqSpecKind = "LLVM recognized-record ABI v1"
  , rocqSpecOrigin =
      "src/Phil/LLVM/RecognizedRecord.hs; src/Phil/LLVM/Lower.hs; src/Phil/LLVM/IR.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/RecognizedRecordABI.v"
  , rocqSpecScope = "Phil.LLVM recognized-record ABI v1"
  , rocqSpecRepresentation = "normalized typed target-operation model"
  , rocqSpecSubjects =
      [ "LLVMRecognizeRecord"
      , "LLVMFieldProjection"
      , "LLVMRuntimeScalarBranch"
      ]
  , rocqSpecTheorems =
      [ "verified_recognized_record_abi_rechecks_systems_source"
      , "verified_recognized_record_abi_preserves_single_recognition_call"
      , "verified_recognized_record_abi_uses_exact_fail_closed_status"
      , "verified_recognized_record_abi_binds_handle_from_same_result"
      , "verified_recognized_record_abi_preserves_typed_accessor"
      , "verified_recognized_record_abi_feeds_exact_receive"
      , "verified_recognized_record_abi_forbids_layout_access_and_unauthorized_strengthening"
      , "recognized_record_abi_status_drift_is_rejected"
      , "recognized_record_abi_record_drift_is_rejected"
      , "recognized_record_abi_width_drift_is_rejected"
      , "recognized_record_abi_consumer_drift_is_rejected"
      , "recognized_record_abi_layout_access_is_rejected"
      , "recognized_record_abi_unauthorized_pointer_strengthening_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/RecognizedRecordABI.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/RecognizedRecordABI.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-REC-ABI-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-REC-ABI-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness, LLVM textual/semantic correspondence, runtime implementation of the opaque-handle/accessor ABI, target calling convention, and Haskell-to-normalized-proof correspondence remain explicit trust boundaries."
  }

llvmRuntimeSymbolCertificationSpec :: RocqCertificationSpec
llvmRuntimeSymbolCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-runtime-symbol-identity"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-RUNTIME-SYM-001"
  , rocqSpecClaim =
      "Under recognized-record ABI v1, a runtime linker symbol is determined by physical runtime primitive identity plus ABI signature, not by RevisionId, EvidenceEntryId, AssuranceUseId, or assurance-claim cardinality/order. Assurance identity remains attached to translation-validation relations rather than linker names; the current singleton-site model must preserve one physical source site as one LLVM call and must not derive extra calls from assurance identity."
  , rocqSpecKind = "LLVM runtime symbol identity"
  , rocqSpecOrigin =
      "docs/phase-0/recognized-record-abi-v1-runtime-symbol-amendment.md; src/Phil/LLVM/IR.hs; src/Phil/LLVM/Lower.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/RuntimeSymbolIdentity.v"
  , rocqSpecScope = "Phil.LLVM runtime symbol identity / singleton site"
  , rocqSpecRepresentation = "physical primitive/signature symbol function"
  , rocqSpecSubjects =
      [ "RuntimeSiteRef"
      , "runtime primitive symbol"
      , "singleton physical site"
      ]
  , rocqSpecTheorems =
      [ "verified_runtime_symbol_uses_physical_primitive_and_signature"
      , "runtime_symbol_is_independent_of_revision_evidence_use_and_claim_count"
      , "verified_singleton_runtime_site_remains_one_llvm_call"
      , "verified_runtime_symbol_does_not_encode_assurance_identity"
      , "evidence_derived_runtime_symbol_is_rejected"
      , "runtime_symbol_drift_is_rejected"
      , "runtime_call_duplication_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/RuntimeSymbolIdentity.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/RuntimeSymbolIdentity.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-RUNTIME-SYM-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-RUNTIME-SYM-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "The present RuntimeSiteRef carries one revision/evidence pair, so this proof establishes the singleton-site symbol/assurance separation only. Arbitrary nonempty claim-set preservation remains deferred to the generalized physical-site model."
  }

knownRecognizedRecordRocqCertificationSpec :: Text -> Maybe RocqCertificationSpec
knownRecognizedRecordRocqCertificationSpec profile
  | profile == rocqSpecProfile systemsRecognizedRecordCertificationSpec =
      Just systemsRecognizedRecordCertificationSpec
  | profile == rocqSpecProfile llvmRecognizedRecordABICertificationSpec =
      Just llvmRecognizedRecordABICertificationSpec
  | profile == rocqSpecProfile llvmRuntimeSymbolCertificationSpec =
      Just llvmRuntimeSymbolCertificationSpec
  | otherwise = Nothing
