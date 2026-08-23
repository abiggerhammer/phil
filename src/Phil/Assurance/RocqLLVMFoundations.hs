{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqLLVMFoundations
  ( llvmFoundationCertificationSpecs
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types (ArtifactRef (..), EvidenceEntryId (..))
import Phil.Core.Syntax (ObligationId (..))

llvmFoundationCertificationSpecs :: [RocqCertificationSpec]
llvmFoundationCertificationSpecs =
  [ identitySpec
  , preservationSpec
  , strengtheningSpec
  , scalarSpec
  ]

mkSpec
  :: Text -> Text -> Text -> Text -> Text -> Text -> Text -> Text -> [Text] -> Text
  -> RocqCertificationSpec
mkSpec profile obligation claim kind origin source scope representation theorems residual =
  RocqCertificationSpec
    { rocqSpecProfile = profile
    , rocqSpecObligation = ObligationId obligation
    , rocqSpecClaim = claim
    , rocqSpecKind = kind
    , rocqSpecOrigin = origin
    , rocqSpecScope = scope
    , rocqSpecRepresentation = representation
    , rocqSpecSubjects = []
    , rocqSpecTheorems = theorems
    , rocqSpecSourceRef = ArtifactRef source
    , rocqSpecCompiledRef = ArtifactRef (Text.dropEnd 2 source <> ".vo")
    , rocqSpecCertificateRef = ArtifactRef ("certificate:rocq:" <> obligation <> ":v1")
    , rocqSpecEvidenceId = EvidenceEntryId ("evidence." <> obligation <> ".rocq.v1")
    , rocqSpecResidualBoundary = residual
    }

identitySpec :: RocqCertificationSpec
identitySpec = mkSpec
  "llvm-identity"
  "PHIL-LLVM-ID-001"
  "A verified LLVM emission is content-bound end to end: the source contract digest equals the exact verified Systems artifact; the target contract digest equals the canonical LLVM-module digest; stored artifact text equals the deterministic renderer; LLVM language/tool version, target triple, data layout, runtime-ABI digest/profile, and compilation profile all equal the explicitly selected target context."
  "LLVM artifact and target-profile identity binding"
  "src/Phil/LLVM/IR.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/Identity.v"
  "proof/Phil/LLVM/Identity.v"
  "Phil.LLVM exact source/target/text/profile identity gates"
  "opaque digest/text/profile identities"
  [ "verified_llvm_source_digest_is_exact"
  , "verified_llvm_target_digest_is_exact"
  , "verified_llvm_artifact_text_is_renderer_output"
  , "verified_llvm_target_profile_is_exact"
  , "verified_llvm_runtime_abi_is_exact"
  , "verified_llvm_compilation_profile_is_exact"
  , "source_digest_drift_is_rejected"
  , "target_digest_drift_is_rejected"
  , "artifact_text_tampering_is_rejected"
  , "target_triple_drift_is_rejected"
  ]
  "Digest collision resistance and concrete Text serialization remain cryptographic/representation assumptions. The proof target is mandatory exact equality gating over source, target, rendered text, target/runtime-ABI identity, and compilation profile."

preservationSpec :: RocqCertificationSpec
preservationSpec = mkSpec
  "llvm-preservation"
  "PHIL-LLVM-PRESERVE-001"
  "A verified LLVM emission first re-verifies its source Systems artifact, preserves the exact multiset of runtime sites, matches the conservative lowering for all ordinary operations and terminators, gives every source CFG edge exactly one connected LLVM path witness, admits no LLVM CFG edge outside those witnessed paths, and preserves the stage trace and resource/failure relations exactly."
  "LLVM conservative translation preservation"
  "src/Phil/LLVM/Lower.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/Preservation.v"
  "proof/Phil/LLVM/Preservation.v"
  "Phil.LLVM conservative Systems-to-LLVM preservation"
  "normalized runtime multiplicities, ordinary projections, CFG witnesses, and contract relations"
  [ "verified_llvm_rechecks_source_systems_artifact"
  , "verified_llvm_preserves_runtime_site_multiplicity"
  , "verified_llvm_matches_conservative_ordinary_projection"
  , "verified_source_edge_has_exactly_one_connected_witness"
  , "verified_non_source_edge_has_no_witness"
  , "verified_target_edge_is_witnessed_exactly"
  , "verified_llvm_preserves_contract_relations"
  , "missing_runtime_site_is_rejected"
  , "invented_ordinary_projection_is_rejected"
  , "missing_source_edge_witness_is_rejected"
  , "duplicate_source_edge_witness_is_rejected"
  , "disconnected_source_edge_witness_is_rejected"
  , "unwitnessed_target_edge_is_rejected"
  , "trace_relation_drift_is_rejected"
  ]
  "Concrete Map/list enumeration, edge-path extraction, and correspondence to Phil.LLVM.Lower.lowerSystemsConservative remain implementation boundaries. The claim targets runtime/control/ordinary-operation and trace/resource-failure preservation."

strengtheningSpec :: RocqCertificationSpec
strengtheningSpec = mkSpec
  "llvm-strengthening"
  "PHIL-LLVM-STRENGTH-001"
  "A verified LLVM module admits optimizer-strengthening facts only as nonempty, stable declarations with exactly one use at the declared function/block and a matching use kind, backed by an explicitly authorized authority that actually exists in the selected Systems/assurance context. Unjustified unreachable, poison, undef, and freeze reject; an llvm.assume strengthening cannot substitute for a runtime-bound mechanism because runtime and ordinary-projection preservation remain mandatory."
  "LLVM explicit strengthening and defined-execution authority"
  "src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/Strengthening.v"
  "proof/Phil/LLVM/Strengthening.v"
  "Phil.LLVM strengthening authority and defined-execution discipline"
  "normalized strengthening declarations/uses/authority map and forbidden LLVM primitives"
  [ "verified_strengthening_use_has_declaration"
  , "verified_strengthening_key_matches_stable_id"
  , "verified_strengthening_claim_is_nonempty"
  , "verified_strengthening_location_exists"
  , "verified_strengthening_has_exactly_one_use"
  , "verified_strengthening_use_location_is_exact"
  , "verified_strengthening_use_kind_matches_location"
  , "verified_strengthening_authority_is_permitted"
  , "verified_strengthening_authority_exists"
  , "poison_is_rejected"
  , "undef_is_rejected"
  , "freeze_is_rejected"
  , "unjustified_unreachable_is_rejected"
  , "assume_cannot_replace_missing_runtime_enforcement"
  ]
  "Authorization-map construction and concrete LLVM syntax/rendering remain correspondence boundaries. The theorem establishes exact location/use/kind/authority gating and exclusion of unmodeled undefined-behavior-strengthening primitives."

scalarSpec :: RocqCertificationSpec
scalarSpec = mkSpec
  "llvm-scalar"
  "PHIL-LLVM-SCALAR-001"
  "Conservative Systems -> LLVM lowering preserves each scalar literal's SSA identity, scalar type/width, and value exactly, and preserves scalar-return identity/type exactly. Ordinary-projection validation must reject any scalar name, width, value, or return-type drift."
  "LLVM scalar preservation"
  "src/Phil/LLVM/IR.hs; src/Phil/LLVM/Lower.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/Scalar.v"
  "proof/Phil/LLVM/Scalar.v"
  "Phil.LLVM scalar ordinary-projection preservation"
  "shared normalized Systems ValueId / LLVM SSA identity with exact ScalarLiteral carry-through"
  [ "verified_llvm_scalar_source_is_systems_verified"
  , "verified_llvm_scalar_literal_preserves_name_type_and_value"
  , "verified_llvm_uint_preserves_exact_width_and_value"
  , "verified_llvm_uint_remains_in_range"
  , "verified_llvm_scalar_return_preserves_identity_and_type"
  , "moved_scalar_ssa_name_is_rejected"
  , "scalar_width_drift_is_rejected"
  , "scalar_value_drift_is_rejected"
  , "scalar_return_identity_drift_is_rejected"
  , "scalar_return_type_drift_is_rejected"
  ]
  "Concrete LLVM rendering/SSA syntax, Haskell lowerer correspondence, and LLVM integer semantics/assembler acceptance remain explicit implementation or external-tool boundaries."
