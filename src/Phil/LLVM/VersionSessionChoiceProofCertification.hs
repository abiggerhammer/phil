{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.VersionSessionChoiceProofCertification
  ( systemsVersionSessionChoiceCertificationSpec
  , llvmVersionSessionChoiceBoundaryCertificationSpec
  ) where

import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

systemsVersionSessionChoiceCertificationSpec :: RocqCertificationSpec
systemsVersionSessionChoiceCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-version-session-choice"
  , rocqSpecObligation = ObligationId "PHIL-SYS-VERSION-SESSION-CHOICE-001"
  , rocqSpecClaim =
      "For the verified Phase 0 unsupported/version(selected) semantic session-choice candidate, the proof-bound local choose_supported predecessor authority is preserved as predecessor authority while the successor transfers its exact local none/some control, branch-local selected-version binding, dedicated binder target, and invariant; the server emits exactly one semantic unsupported select with no payload and exactly one semantic version select carrying server.selected_version : UInt16; the client offers exactly unsupported/no-payload and version/client.selected_version : UInt16 with the version binder target dedicated to client.entry; endpoint payload identities remain distinct; client refinement consumes exactly its received selected version; legacy client Bool/receive state is absent; the exact lowering decision is bound; and no physical discriminator, UInt16 wire layout, runtime ABI, or outer framing is selected."
  , rocqSpecKind = "Systems semantic version/unsupported session choice"
  , rocqSpecOrigin =
      "docs/phase-0/version-session-choice-v1.md; src/Phil/Systems/VersionSessionChoice.hs; src/Phil/Systems/Verify.hs; src/Phil/Systems/VersionSessionChoiceProofCheck.hs; proof/Phil/Systems/VersionSessionChoice.v"
  , rocqSpecScope = "Phil.Systems unsupported/version(selected : UInt16) dual session choice"
  , rocqSpecRepresentation =
      "server OpSessionSelect unsupported/version(selected); client TermSessionOffer with branch-local UInt16 version payload"
  , rocqSpecSubjects =
      [ "UploadServer/server.version.choose"
      , "UploadServer/server.unsupported"
      , "UploadServer/server.version"
      , "server.selected_version : UInt16"
      , "UploadClient/client.entry"
      , "client.selected_version : UInt16"
      , "UploadClient/client.version.check"
      , "lower.session.version_choice"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_version_choice_reuses_local_predecessor_authority"
      , "verified_systems_version_choice_transfers_local_choice_authority"
      , "verified_systems_version_choice_preserves_exact_transports"
      , "verified_systems_version_choice_preserves_exact_server_selects"
      , "verified_systems_version_choice_preserves_exact_client_offer"
      , "verified_systems_version_choice_preserves_endpoint_separation_and_refinement"
      , "verified_systems_version_choice_eliminates_legacy_client_choice_and_binds_decision"
      , "verified_systems_version_choice_selects_no_physical_representation"
      , "systems_version_choice_local_or_transport_drift_is_rejected"
      , "systems_version_choice_server_select_drift_is_rejected"
      , "systems_version_choice_client_or_representation_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/VersionSessionChoice.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/VersionSessionChoice.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-VERSION-SESSION-CHOICE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-VERSION-SESSION-CHOICE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell endpoint/block/value/decision identities, generic Systems dedicated-payload-target verification, the exact version-session-choice witness, and the CI-only exact-select multiplicity correspondence checker to the normalized proof model remain explicit trust boundaries. No physical version-choice representation is proved."
  }

llvmVersionSessionChoiceBoundaryCertificationSpec :: RocqCertificationSpec
llvmVersionSessionChoiceBoundaryCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-version-session-choice-boundary"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-VERSION-SESSION-CHOICE-BOUNDARY-001"
  , rocqSpecClaim =
      "For the Phase 0 unsupported/version(selected) semantic session choice before a dedicated physical lowering exists, generic LLVM lowering preserves the proof-bound local-choice predecessor boundary, emits exactly one unlowered-session-select poison marker in each exact server choice block, fails closed at the exact client TermSessionOffer as LLVMUnreachable None, preserves the payload/cancel predecessor lowering boundary, and invents no conditional dispatch, switch, selected-version physical materialization, runtime ABI, discriminator encoding, UInt16 wire layout, outer framing, or TranslationValidated claim."
  , rocqSpecKind = "LLVM fail-closed version session-choice competence boundary"
  , rocqSpecOrigin =
      "src/Phil/LLVM/Lower.hs; test/VersionSessionChoiceMain.hs; src/Phil/Systems/VersionSessionChoiceProofCheck.hs; proof/Phil/LLVM/VersionSessionChoiceBoundary.v"
  , rocqSpecScope = "Phil.LLVM generic lowering boundary for unsupported/version(selected) semantic session choice"
  , rocqSpecRepresentation =
      "server OpSessionSelect -> LLVMPoison; client TermSessionOffer -> LLVMUnreachable None; no version-choice physical ABI"
  , rocqSpecSubjects =
      [ "UploadServer/server.unsupported"
      , "LLVMPoison unlowered-session-select:unsupported"
      , "UploadServer/server.version"
      , "LLVMPoison unlowered-session-select:version"
      , "UploadClient/client.entry"
      , "LLVMUnreachable None"
      , "local choose_supported predecessor boundary"
      , "phil-runtime/phase0/payload-cancel-choice-v1 predecessor target"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_version_choice_boundary_reuses_semantic_and_local_authority"
      , "verified_llvm_version_choice_boundary_marks_exact_server_selects_unlowered"
      , "verified_llvm_version_choice_boundary_fails_closed_at_client_offer"
      , "verified_llvm_version_choice_boundary_preserves_predecessor_boundaries"
      , "verified_llvm_version_choice_boundary_invents_no_physical_representation"
      , "llvm_version_choice_non_fail_closed_server_lowering_is_rejected"
      , "llvm_version_choice_invented_representation_or_translation_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/VersionSessionChoiceBoundary.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/VersionSessionChoiceBoundary.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-VERSION-SESSION-CHOICE-BOUNDARY-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-VERSION-SESSION-CHOICE-BOUNDARY-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from Phil.LLVM.Lower poison/unreachable behavior, exact server-select multiplicity, client-offer fail-closed behavior, and focused Haskell regression coverage to the normalized boundary model remain explicit trust boundaries. This certificate is not translation validation and does not certify a physical unsupported/version encoding."
  }
