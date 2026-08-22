{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqStorage
  ( systemsStorageCertificationSpec
  , llvmStorageCertificationSpec
  , knownStorageRocqCertificationSpec
  ) where

import Data.Text (Text)
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

systemsStorageCertificationSpec :: RocqCertificationSpec
systemsStorageCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-storage"
  , rocqSpecObligation = ObligationId "PHIL-SYS-STORAGE-001"
  , rocqSpecClaim =
      "For the verified Phase 0 storage candidate, digest success reaches the exact storage block; the exact payload OwnedBuffer is transferred to exactly one StorageBoundary TermStore on all outcomes; the exact semantic result is RuntimeScalar UploadId; success/failure edges are exact; and Phil source performs no release or partial cleanup of the transferred owner in the store, success, or failure blocks. Provider persistence/free behavior and UploadId representation remain outside this Systems theorem."
  , rocqSpecKind = "Systems storage ownership semantics"
  , rocqSpecOrigin =
      "src/Phil/Systems/Storage.hs; src/Phil/Systems/DigestValidation.hs; proof/Phil/Systems/Storage.v"
  , rocqSpecScope = "Phil.Systems storage boundary"
  , rocqSpecRepresentation = "normalized digest-predecessor / owner-transfer / UploadId-result model"
  , rocqSpecSubjects =
      [ "OwnedBuffer server.payload"
      , "RuntimeScalar UploadId server.upload_id"
      , "StorageBoundary TermStore"
      , "storage success/failure edges"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_storage_reuses_digest_authority"
      , "verified_systems_storage_digest_success_enters_exact_store"
      , "verified_systems_storage_transfers_exact_payload_owner_once"
      , "verified_systems_storage_produces_exact_upload_id_result"
      , "verified_systems_storage_preserves_exact_success_and_failure_edges"
      , "verified_systems_storage_has_no_post_transfer_release"
      , "systems_storage_owner_drift_is_rejected"
      , "systems_storage_result_identity_or_role_drift_is_rejected"
      , "systems_storage_multiplicity_or_boundary_drift_is_rejected"
      , "systems_storage_predecessor_or_block_drift_is_rejected"
      , "systems_storage_edge_drift_is_rejected"
      , "systems_storage_missing_ownership_transfer_is_rejected"
      , "systems_storage_post_transfer_release_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/Storage.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/Storage.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-STORAGE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-STORAGE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell Text/ValueId/BlockId identities, map enumeration, TermStore multiplicity, ownership-transfer semantics, RuntimeScalar UploadId role, and post-transfer release detection to the normalized proof model remain explicit trust boundaries. Concrete persistence/free behavior is not proved here."
  }

llvmStorageCertificationSpec :: RocqCertificationSpec
llvmStorageCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-storage"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-STORAGE-001"
  , rocqSpecClaim =
      "For the verified storage-v1 target, lowering passes the exact digest/exact-receive payload owner to phil_runtime_store(ptr), preserves the exact semantic UploadId result identity, transfers payload ownership without generated post-transfer release, accepts only exact status 1 with exact success/failure edges, keeps UploadId opaque runtime-managed non-owning and valid by identity through component return, preserves physical runtime-symbol authority, and rejects payload/result/status/edge drift, ambient or nullary storage, UploadId layout/release, or unauthorized strengthening. Provider-side failure-null UploadId is external ABI conformance and is not assumed by the fail-closed consumer theorem."
  , rocqSpecKind = "LLVM storage ABI v1"
  , rocqSpecOrigin =
      "docs/phase-0/storage-abi-v1.md; src/Phil/LLVM/Storage.hs; src/Phil/LLVM/Lower.hs; src/Phil/LLVM/IR.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/Storage.v"
  , rocqSpecScope = "Phil.LLVM storage-v1"
  , rocqSpecRepresentation = "normalized owner-consuming store / fail-closed status / opaque UploadId model"
  , rocqSpecSubjects =
      [ "LLVMStore"
      , "exact payload-owner operand"
      , "opaque UploadId result"
      , "status == 1 fail-closed branch"
      , "physical storage runtime symbol"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_storage_reuses_systems_storage_authority"
      , "verified_llvm_storage_reuses_digest_authority"
      , "verified_llvm_storage_reuses_runtime_symbol_authority"
      , "verified_llvm_storage_preserves_exact_payload_owner_from_digest"
      , "verified_llvm_storage_preserves_exact_upload_id_identity_and_opacity"
      , "verified_llvm_storage_uses_exact_status_one_and_exact_edges"
      , "verified_llvm_storage_transfers_owner_without_generated_release"
      , "verified_llvm_storage_forbids_upload_id_layout_release_ambient_state_and_strengthening"
      , "llvm_storage_payload_identity_drift_is_rejected"
      , "llvm_storage_upload_id_identity_drift_is_rejected"
      , "llvm_storage_status_drift_is_rejected"
      , "llvm_storage_edge_drift_is_rejected"
      , "llvm_storage_missing_transfer_or_post_transfer_release_is_rejected"
      , "llvm_storage_upload_id_representation_drift_is_rejected"
      , "llvm_storage_ambient_or_strengthening_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/Storage.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/Storage.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-STORAGE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-STORAGE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed correspondence from Systems storage owner/result identities through deterministic LLVM SSA names, LLVMStore rendering and status comparison to the normalized model; opaque runtime handle representation; target calling convention; provider ABI conformance; persistence/ownership consumption; and native execution remain explicit trust boundaries. Failure-null UploadId behavior is not a theorem premise."
  }

knownStorageRocqCertificationSpec :: Text -> Maybe RocqCertificationSpec
knownStorageRocqCertificationSpec profile
  | profile == rocqSpecProfile systemsStorageCertificationSpec =
      Just systemsStorageCertificationSpec
  | profile == rocqSpecProfile llvmStorageCertificationSpec =
      Just llvmStorageCertificationSpec
  | otherwise = Nothing
