{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.LocalRuntimeChoiceProofCertification
  ( systemsLocalRuntimeChoiceCertificationSpec
  , llvmLocalRuntimeChoiceBoundaryCertificationSpec
  ) where

import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

systemsLocalRuntimeChoiceCertificationSpec :: RocqCertificationSpec
systemsLocalRuntimeChoiceCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-local-runtime-choice"
  , rocqSpecObligation = ObligationId "PHIL-SYS-LOCAL-RUNTIME-CHOICE-001"
  , rocqSpecClaim =
      "For the verified Phase 0 choose_supported candidate, local none/some authority remains distinct from peer/session choice; none carries no payload; some binds the exact branch-local UInt16 selected version at the some target; the some binder target has the choice block as sole predecessor; the none arm cannot observe the some payload; the exact generic select-version consumer receives server.transport then server.selected_version; the legacy has_version Bool and choose_supported output call are absent; the stable version-selection invariant is transferred to exact InvariantRuntimeChoice authority; the exact lowering decision is preserved; and proof-bound payload/cancel semantic authority remains available."
  , rocqSpecKind = "Systems local runtime choice with branch-local payload"
  , rocqSpecOrigin =
      "docs/phase-0/local-runtime-choice-systems-v1.md; src/Phil/Systems/LocalRuntimeChoice.hs; proof/Phil/Systems/LocalRuntimeChoice.v"
  , rocqSpecScope = "Phil.Systems local choose_supported none/some choice"
  , rocqSpecRepresentation =
      "TermRuntimeChoice choose_supported with none/no-payload and some/UInt16 branch-edge binding"
  , rocqSpecSubjects =
      [ "UploadServer/server.version.choose"
      , "choose_supported"
      , "none -> server.unsupported"
      , "some(server.selected_version : UInt16) -> server.version"
      , "invariant.version.selection_branch"
      , "lower.local.choose_supported"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_local_choice_reuses_payload_cancel_authority"
      , "verified_systems_local_choice_preserves_local_choice_authority"
      , "verified_systems_local_choice_preserves_exact_none_some_arms"
      , "verified_systems_local_choice_preserves_branch_local_selected_version"
      , "verified_systems_local_choice_preserves_exact_version_consumer"
      , "verified_systems_local_choice_eliminates_legacy_boolean_projection"
      , "verified_systems_local_choice_transfers_invariant_and_lowering_authority"
      , "systems_local_choice_authority_or_arm_drift_is_rejected"
      , "systems_local_choice_payload_or_predecessor_drift_is_rejected"
      , "systems_local_choice_consumer_legacy_or_invariant_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/LocalRuntimeChoice.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/LocalRuntimeChoice.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-LOCAL-RUNTIME-CHOICE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-LOCAL-RUNTIME-CHOICE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell function/block/value/invariant/decision identities, exact TermRuntimeChoice shape, CFG predecessor enumeration, scalar dataflow, and exact generic select-version operation to the normalized proof model remain explicit trust boundaries. No physical representation of choose_supported or version(selected) is proved."
  }

llvmLocalRuntimeChoiceBoundaryCertificationSpec :: RocqCertificationSpec
llvmLocalRuntimeChoiceBoundaryCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-local-runtime-choice-boundary"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-LOCAL-RUNTIME-CHOICE-BOUNDARY-001"
  , rocqSpecClaim =
      "For the Phase 0 local choose_supported choice before a dedicated backend lowering exists, generic LLVM lowering fails closed at the exact local-choice block with LLVMUnreachable None, while prior payload/cancel ABI/lowering authority remains available. No conditional branch, switch, physical chooser primitive, selected-version materialization, chooser ABI extension, version wire encoding, or TranslationValidated claim is invented for the unlowered local choice."
  , rocqSpecKind = "LLVM fail-closed backend competence boundary"
  , rocqSpecOrigin =
      "src/Phil/LLVM/Lower.hs; test/LocalRuntimeChoiceMain.hs; proof/Phil/LLVM/LocalRuntimeChoiceBoundary.v"
  , rocqSpecScope = "Phil.LLVM generic lowering boundary for TermRuntimeChoice"
  , rocqSpecRepresentation =
      "unlowered TermRuntimeChoice -> LLVMUnreachable None; no local-choice physical ABI"
  , rocqSpecSubjects =
      [ "UploadServer/server.version.choose"
      , "TermRuntimeChoice choose_supported"
      , "LLVMUnreachable None"
      , "phil-runtime/phase0/payload-cancel-choice-v1 predecessor target"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_local_choice_boundary_reuses_semantic_and_payload_cancel_authority"
      , "verified_llvm_local_choice_fails_closed_at_exact_choice_block"
      , "verified_llvm_local_choice_invents_no_physical_representation"
      , "verified_llvm_local_choice_preserves_predecessor_target_without_claiming_translation"
      , "llvm_local_choice_non_fail_closed_lowering_is_rejected"
      , "llvm_local_choice_invented_representation_or_certification_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/LocalRuntimeChoiceBoundary.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/LocalRuntimeChoiceBoundary.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-LOCAL-RUNTIME-CHOICE-BOUNDARY-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-LOCAL-RUNTIME-CHOICE-BOUNDARY-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from generic Phil.LLVM.Lower behavior and focused Haskell regression coverage to the normalized boundary model remain explicit trust boundaries. This certificate is not translation validation and does not certify a physical choose_supported representation."
  }
