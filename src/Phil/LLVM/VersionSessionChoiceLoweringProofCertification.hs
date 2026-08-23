{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.VersionSessionChoiceLoweringProofCertification
  ( systemsVersionChoiceOperandsCertificationSpec
  , llvmVersionSessionChoiceLoweringCertificationSpec
  ) where

import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

systemsVersionChoiceOperandsCertificationSpec :: RocqCertificationSpec
systemsVersionChoiceOperandsCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-version-choice-operands"
  , rocqSpecObligation = ObligationId "PHIL-SYS-VERSION-CHOICE-OPERANDS-001"
  , rocqSpecClaim =
      "For the landed Phase 0 version-choice operand materialization, proof-bound unsupported/version semantic predecessor authority is preserved; server.supported_versions is the exact SupportedVersions RuntimeInput and has no local producer; recognized Hello is materialized after ingress commit and projected exactly once to server.hello_versions : RuntimeOpaque VersionSet; choose_supported receives exactly [server.supported_versions, server.hello_versions], preserves none/some arms, branch-local selected UInt16 binding, invariant, exact server semantic select multiplicity, client offer/refinement authority, payload/cancel authority, and the exact lowering decision; provider set semantics and tie-breaking remain unclaimed external obligations."
  , rocqSpecKind = "Systems explicit version-choice runtime operands"
  , rocqSpecOrigin =
      "src/Phil/Systems/VersionChoiceOperands.hs; proof/Phil/Systems/VersionChoiceOperands.v"
  , rocqSpecScope = "Phil.Systems explicit choose_supported inputs and recognized Hello.versions provenance"
  , rocqSpecRepresentation =
      "server.supported_versions RuntimeInput + server.hello RuntimeRecord + server.hello_versions RuntimeOpaque feeding TermRuntimeChoice choose_supported"
  , rocqSpecSubjects =
      [ "UploadServer/server.hello.commit"
      , "server.supported_versions : RuntimeInput[SupportedVersions]"
      , "server.hello : RuntimeRecord[Hello]"
      , "server.hello_versions : RuntimeOpaque[VersionSet]"
      , "UploadServer/server.version.choose"
      , "server.selected_version : UInt16"
      , "lower.version.choice.operands"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_version_operands_reuses_semantic_authority"
      , "verified_systems_version_operands_materializes_exact_runtime_values"
      , "verified_systems_version_operands_preserves_commit_projection_order"
      , "verified_systems_version_operands_binds_exact_chooser_inputs"
      , "verified_systems_version_operands_preserves_session_and_refinement_authority"
      , "verified_systems_version_operands_binds_lowering_decision_without_provider_claim"
      , "systems_version_operands_value_or_projection_drift_is_rejected"
      , "systems_version_operands_chooser_session_or_provider_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/VersionChoiceOperands.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/VersionChoiceOperands.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-VERSION-CHOICE-OPERANDS-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-VERSION-CHOICE-OPERANDS-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell value roles, producer analysis, ingress-commit operation ordering, materialization/projection operations, chooser operand order, invariant/decision identities, and the CI-only exact-final-candidate multiplicity checker to the normalized proof model remain explicit trust boundaries. Runtime provider set semantics and tie-breaking are not proved."
  }

llvmVersionSessionChoiceLoweringCertificationSpec :: RocqCertificationSpec
llvmVersionSessionChoiceLoweringCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-version-session-choice-lowering"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-VERSION-SESSION-CHOICE-001"
  , rocqSpecClaim =
      "For phil-runtime/phase0/version-session-choice-v1, verified lowering preserves the exact target/layout/profile, explicit serverSupported parameter and recognized Hello.versions projection, emits exactly one choose_supported primitive with exact two inputs, selected UInt16 output and none/some targets, exactly one unsupported selector and one version selector with exact transport/payload, exactly one client payload binding and transport-scoped selected-version refinement with exact targets, binds unsupported=0x00 and version=0x01||UInt16BE while leaving outer framing undefined, preserves payload/cancel predecessor authority, eliminates unlowered poison/generic/ambient version state, and keeps provider semantics, prior-Hello association, concrete I/O, malformed termination, write success, LLVM correctness, linking, and native execution outside the Rocq claim."
  , rocqSpecKind = "LLVM version session-choice ABI v1 lowering"
  , rocqSpecOrigin =
      "docs/phase-0/version-session-choice-abi-v1.md; src/Phil/LLVM/VersionSessionChoice.hs; src/Phil/LLVM/VersionSessionChoiceLoweringProofCheck.hs; proof/Phil/LLVM/VersionSessionChoiceLowering.v"
  , rocqSpecScope = "Phil.LLVM version-session-choice-v1 explicit chooser/select/receive/refinement lowering"
  , rocqSpecRepresentation =
      "explicit projection + LLVMChooseSupported + selectors + LLVMVersionChoiceOffer + LLVMVersionRefinement"
  , rocqSpecSubjects =
      [ "phil_record_Hello_get_versions(ptr)->ptr"
      , "phil_runtime_choose_supported(ptr,ptr,ptr)->i1"
      , "phil_runtime_select_unsupported(ptr)->void"
      , "phil_runtime_select_version(ptr,i16)->void"
      , "phil_runtime_receive_version_choice(ptr,ptr)->i1"
      , "phil_runtime_refine_selected_version(ptr,i16)->i1"
      , "wire unsupported=0x00"
      , "wire version=0x01 || UInt16BE"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_version_choice_reuses_systems_and_payload_cancel_authority"
      , "verified_llvm_version_choice_preserves_exact_target_and_projection"
      , "verified_llvm_version_choice_lowers_exact_chooser"
      , "verified_llvm_version_choice_lowers_exact_server_selectors"
      , "verified_llvm_version_choice_lowers_exact_client_offer_and_refinement"
      , "verified_llvm_version_choice_binds_wire_profile_without_ambient_or_generic_state"
      , "verified_llvm_version_choice_keeps_operational_gates_external"
      , "llvm_version_choice_chooser_or_selector_drift_is_rejected"
      , "llvm_version_choice_client_ambient_or_gate_conflation_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/VersionSessionChoiceLowering.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/VersionSessionChoiceLowering.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-VERSION-SESSION-CHOICE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-VERSION-SESSION-CHOICE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed Systems/LLVM-to-normalized-proof correspondence; provider choose_supported set semantics; exact transport-local association with the versions sent in the prior client Hello; opaque set representation; concrete byte I/O; malformed-input non-return; physical write success; provider ABI conformance; LLVM implementation correctness; whole-program linking; and native execution remain explicit trust boundaries."
  }
