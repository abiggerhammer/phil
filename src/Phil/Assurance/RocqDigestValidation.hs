{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqDigestValidation
  ( systemsDigestValidationCertificationSpec
  , llvmDigestValidationCertificationSpec
  , knownDigestValidationRocqCertificationSpec
  ) where

import Data.Text (Text)
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

systemsDigestValidationCertificationSpec :: RocqCertificationSpec
systemsDigestValidationCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-digest-validation"
  , rocqSpecObligation = ObligationId "PHIL-SYS-DIGEST-001"
  , rocqSpecClaim =
      "For the verified Phase 0 DigestMatches candidate, the digest runtime check carries exactly two ordered semantic subjects: the exact recognized Begin RuntimeRecord and the exact payload BorrowedSlice; the view is produced by exactly one matching borrow of the exact payload owner before the digest check, and record/borrow/arity/order/boundary drift rejects."
  , rocqSpecKind = "Systems digest subject and borrow semantics"
  , rocqSpecOrigin =
      "src/Phil/Systems/DigestValidation.hs; src/Phil/Systems/RecognizedRecord.hs; proof/Phil/Systems/DigestValidation.v"
  , rocqSpecScope = "Phil.Systems DigestMatches(begin,payloadView)"
  , rocqSpecRepresentation = "normalized recognized-record / owner-borrow / ordered-subject model"
  , rocqSpecSubjects =
      [ "RuntimeRecord Begin"
      , "OwnedBuffer server.payload"
      , "BorrowedSlice server.payload_view"
      , "DigestBoundary ordered subjects"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_digest_reuses_recognized_record_authority"
      , "verified_systems_digest_uses_exact_recognized_record_subject"
      , "verified_systems_digest_borrows_exact_payload_owner_once"
      , "verified_systems_digest_orders_borrow_before_check"
      , "verified_systems_digest_preserves_exact_ordered_subject_pair"
      , "verified_systems_digest_uses_digest_boundary"
      , "systems_digest_record_subject_drift_is_rejected"
      , "systems_digest_borrow_owner_drift_is_rejected"
      , "systems_digest_competing_or_missing_borrow_is_rejected"
      , "systems_digest_late_borrow_is_rejected"
      , "systems_digest_subject_arity_drift_is_rejected"
      , "systems_digest_subject_order_or_identity_drift_is_rejected"
      , "systems_digest_non_digest_boundary_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/DigestValidation.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/DigestValidation.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-DIGEST-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-DIGEST-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell Text/ValueId/BlockId identities, Data.Map/list enumeration, operation ordering, RuntimeRecord/BorrowedSlice roles, and DigestValidationWitness verification to the normalized proof model remain explicit trust boundaries."
  }

llvmDigestValidationCertificationSpec :: RocqCertificationSpec
llvmDigestValidationCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-digest-validation"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-DIGEST-001"
  , rocqSpecClaim =
      "For the verified digest-validation-v1 target, lowering maps the exact recognized Begin semantic subject to the exact opaque record operand and the exact payload borrow owner to the exact opaque payload-owner operand, preserves the ordered two-operand pair and source-derived success/failure edges, erases only the borrow view representation by reusing the owner pointer with no copy, binds SHA-256 as part of runtime ABI identity, preserves physical runtime-symbol identity, and rejects ambient subjects, nullary digest validation, layout access, unauthorized pointer strengthening, or identity/order/mechanism drift."
  , rocqSpecKind = "LLVM digest validation ABI v1"
  , rocqSpecOrigin =
      "docs/phase-0/digest-validation-abi-v1.md; src/Phil/LLVM/DigestValidation.hs; src/Phil/LLVM/Lower.hs; src/Phil/LLVM/IR.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/DigestValidation.v"
  , rocqSpecScope = "Phil.LLVM digest-validation-v1"
  , rocqSpecRepresentation = "normalized two-operand digest target / no-copy borrow-erasure / ABI-mechanism model"
  , rocqSpecSubjects =
      [ "LLVMDigestValidate"
      , "recognized Begin opaque handle"
      , "exact receive payload-owner handle"
      , "BorrowedSlice(owner) -> same owner ptr"
      , "SHA-256 ABI mechanism identity"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_digest_reuses_systems_subject_and_borrow_authority"
      , "verified_llvm_digest_reuses_exact_receive_authority"
      , "verified_llvm_digest_reuses_runtime_symbol_authority"
      , "verified_llvm_digest_preserves_exact_recognized_record_operand"
      , "verified_llvm_digest_preserves_exact_payload_owner_and_erases_only_view_representation"
      , "verified_llvm_digest_preserves_exact_ordered_operand_pair"
      , "verified_llvm_digest_preserves_source_success_and_failure_edges"
      , "verified_llvm_digest_binds_sha256_as_abi_mechanism"
      , "verified_llvm_digest_forbids_ambient_state_layout_access_and_unauthorized_strengthening"
      , "llvm_digest_record_operand_drift_is_rejected"
      , "llvm_digest_payload_operand_drift_is_rejected"
      , "llvm_digest_operand_order_or_arity_drift_is_rejected"
      , "llvm_digest_borrow_representation_drift_is_rejected"
      , "llvm_digest_mechanism_or_abi_binding_drift_is_rejected"
      , "llvm_digest_edge_drift_is_rejected"
      , "llvm_digest_ambient_or_nullary_state_is_rejected"
      , "llvm_digest_layout_access_or_strengthening_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/DigestValidation.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/DigestValidation.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-DIGEST-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-DIGEST-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed correspondence from Systems ValueId/borrow identity through deterministic LLVM SSA naming and LLVMDigestValidate rendering to the normalized model; runtime opaque-handle representation; target calling convention; and concrete provider/libcrypto behavior remain explicit trust boundaries. SHA-256 correctness is not proved here."
  }

knownDigestValidationRocqCertificationSpec :: Text -> Maybe RocqCertificationSpec
knownDigestValidationRocqCertificationSpec profile
  | profile == rocqSpecProfile systemsDigestValidationCertificationSpec =
      Just systemsDigestValidationCertificationSpec
  | profile == rocqSpecProfile llvmDigestValidationCertificationSpec =
      Just llvmDigestValidationCertificationSpec
  | otherwise = Nothing
