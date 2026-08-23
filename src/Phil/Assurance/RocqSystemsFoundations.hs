{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqSystemsFoundations
  ( systemsFoundationCertificationSpecs
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types (ArtifactRef (..), EvidenceEntryId (..))
import Phil.Core.Syntax (ObligationId (..))

systemsFoundationCertificationSpecs :: [RocqCertificationSpec]
systemsFoundationCertificationSpecs =
  [ identitySpec
  , ownershipSpec
  , factDispositionSpec
  , runtimeSpec
  , scalarSpec
  , scalarDataflowSpec
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
  "systems-identity"
  "PHIL-SYS-ID-001"
  "A verified systems artifact is content-bound end to end: the stage source digest equals the trusted source artifact; the stage target digest equals the systems-program digest; the assurance manifest implementation digest equals the complete systems-artifact digest; every lowering decision is bound to the same source/target digests and its own content digest; the lowering-ledger root is recomputed from those decision digests and must equal the manifest lowering root."
  "Systems artifact and lowering identity binding"
  "src/Phil/Systems/IR.hs; src/Phil/Systems/Verify.hs; proof/Phil/Systems/Identity.v"
  "proof/Phil/Systems/Identity.v"
  "Phil.Systems identity and lowering-ledger gates"
  "opaque digest identities and normalized lowering-decision bindings"
  [ "verified_source_is_exact_trusted_source"
  , "verified_target_is_exact_program_digest"
  , "verified_manifest_binds_complete_systems_artifact"
  , "verified_manifest_lowering_root_is_recomputed_root"
  , "verified_decision_has_nonempty_stable_identity"
  , "verified_decision_key_matches_embedded_identity"
  , "verified_decision_digest_is_recomputed_digest"
  , "verified_decision_is_bound_to_stage_artifacts"
  , "verified_decision_is_bound_end_to_end"
  ]
  "The proof establishes equality-gating and shared identity structure, not SHA-256 collision resistance or injectivity of concrete serialization. Concrete digest computation and container correspondence remain implementation boundaries."

ownershipSpec :: RocqCertificationSpec
ownershipSpec = mkSpec
  "systems-ownership"
  "PHIL-SYS-OWN-001"
  "A verified systems program cannot duplicate owning storage; borrowed slices must name an existing owning value and remain non-owning; a recognition terminator must operate on a pending ingress and a borrow of its frame owner, its success branch commits that pending ingress before any subsequent transport use, and its failure branch destroys the pending ingress. Orphan commit/destroy operations reject."
  "Systems ownership and recognition realization"
  "src/Phil/Systems/Verify.hs; proof/Phil/Systems/Ownership.v"
  "proof/Phil/Systems/Ownership.v"
  "Phil.Systems ownership and recognition relations"
  "normalized value/storage ownership and recognition-parent relations"
  [ "verified_storage_has_at_most_one_owner"
  , "verified_borrow_names_existing_owner"
  , "borrowed_value_is_not_an_owner"
  , "verified_recognition_raw_view_borrows_frame_owner"
  , "verified_recognition_success_commits_exact_pending"
  , "verified_recognition_failure_destroys_exact_pending"
  , "verified_recognition_has_no_transport_use_before_commit"
  , "verified_commit_has_recognition_success_parent"
  , "verified_destroy_has_recognition_failure_parent"
  , "orphan_commit_is_rejected"
  , "orphan_destroy_is_rejected"
  ]
  "Concrete Map traversal, textual storage identities, operation-list extraction, and correspondence to normalized owner/recognition relations remain implementation boundaries."

factDispositionSpec :: RocqCertificationSpec
factDispositionSpec = mkSpec
  "systems-fact-disposition"
  "PHIL-SYS-FACT-001"
  "A verified stage contract covers exactly the trusted source-fact set with no duplicate or empty fact IDs. Facts designated as requiring transfer cannot be merely consumed. A transferred fact names at least one checked stage invariant; an erased fact requires a selected exact erasure use plus a matching lowering decision and program erasure operation; runtime-retained evidence is selected and revision-aligned; derived facts name selected obligations. An Erase lowering decision must preserve the source fact through at least one transferred invariant or selected derived obligation."
  "Systems stage-fact disposition preservation"
  "src/Phil/Systems/Verify.hs; proof/Phil/Systems/FactDisposition.v"
  "proof/Phil/Systems/FactDisposition.v"
  "Phil.Systems stage-contract fact disposition"
  "normalized partial fact map with one checked semantic-carrier witness"
  [ "verified_stage_covers_exact_trusted_fact_set"
  , "verified_stage_has_no_empty_fact_identity"
  , "normalized_stage_fact_identity_is_unique"
  , "required_transfer_fact_cannot_be_consumed"
  , "transferred_fact_has_checked_invariant"
  , "erased_fact_requires_exact_selected_erasure_chain"
  , "runtime_retained_fact_uses_selected_evidence"
  , "runtime_retained_fact_preserves_revision_alignment"
  , "derived_fact_names_selected_obligation"
  , "verified_erasure_has_surviving_semantic_carrier"
  ]
  "Concrete stage IDs, Haskell list/map normalization, and invariant-claim correspondence remain implementation boundaries. Additional transferred invariants do not weaken the one-witness authority rule."

runtimeSpec :: RocqCertificationSpec
runtimeSpec = mkSpec
  "systems-runtime"
  "PHIL-SYS-RUNTIME-001"
  "Every systems runtime site cites selected RuntimeEnforced evidence for the same obligation revision and a cost reference declared by that evidence, with the expected runtime-site kind when specified. Every selected retained-runtime use has exactly one matching site. CertifiedRelease contains no defensive diagnostics; CheckedRuntime diagnostics require a DefensiveProfile lowering decision. Copy operations require Copy lowering decisions with an explicit byte-copy cost; RemoveCheck cannot discard RuntimeEnforced evidence."
  "Systems runtime and ADR-011 cost realization"
  "src/Phil/Systems/Verify.hs; proof/Phil/Systems/Runtime.v"
  "proof/Phil/Systems/Runtime.v"
  "Phil.Systems runtime-site/evidence/cost/profile realization"
  "normalized runtime evidence, site multiplicity, profile, and lowering-action model"
  [ "verified_runtime_site_uses_selected_evidence"
  , "verified_runtime_site_requires_runtime_enforced_kind"
  , "verified_runtime_site_preserves_revision"
  , "verified_runtime_site_uses_declared_cost"
  , "specified_runtime_site_kind_is_exact"
  , "verified_retained_runtime_use_has_exactly_one_site"
  , "retained_runtime_use_with_no_site_is_rejected"
  , "retained_runtime_use_with_duplicate_sites_is_rejected"
  , "certified_release_has_no_verified_diagnostic"
  , "checked_runtime_diagnostic_requires_defensive_cost"
  , "verified_copy_requires_copy_lowering_decision"
  , "verified_copy_has_explicit_byte_cost"
  , "verified_remove_check_cannot_drop_runtime_enforced_evidence"
  ]
  "Concrete runtime-site enumeration and textual cost-shape rendering remain implementation correspondence boundaries. The theorem establishes selected evidence/revision/cost alignment and ADR-011 profile classification."

scalarSpec :: RocqCertificationSpec
scalarSpec = mkSpec
  "systems-scalar"
  "PHIL-SYS-SCALAR-001"
  "A Systems scalar literal is valid only when its output exists, is TypedScalar of exactly the literal's intrinsic type, and the literal is in range. TermReturnScalar must reference an existing TypedScalar value, and all scalar-returning exits of one function must agree on one scalar type."
  "Systems scalar typing and return"
  "src/Phil/Systems/IR.hs; src/Phil/Systems/Verify.hs; proof/Phil/Systems/Scalar.v"
  "proof/Phil/Systems/Scalar.v"
  "Phil.Systems scalar literal and return checks"
  "normalized scalar value/type/return maps"
  [ "verified_systems_literal_is_valid_and_exactly_typed"
  , "verified_systems_return_names_scalar_value"
  , "verified_systems_scalar_returns_have_one_type"
  , "missing_scalar_literal_output_is_rejected"
  , "mismatched_scalar_literal_type_is_rejected"
  , "out_of_range_scalar_literal_is_rejected"
  , "non_scalar_return_is_rejected"
  , "mismatched_scalar_return_types_are_rejected"
  ]
  "Concrete Data.Map enumeration/lookup and correspondence to the Haskell Systems verifier remain implementation boundaries. Core scalar range/type semantics are separately certified."

scalarDataflowSpec :: RocqCertificationSpec
scalarDataflowSpec = mkSpec
  "systems-scalar-dataflow"
  "PHIL-SYS-SSA-001"
  "Every TypedScalar value has exactly one definition, and every scalar use is dominated by that definition (or follows it earlier in the same block); missing, duplicate, and use-before-definition or non-dominating definitions must reject."
  "Systems scalar SSA and dataflow"
  "src/Phil/Systems.hs; proof/Phil/Systems/ScalarDataflow.v"
  "proof/Phil/Systems/ScalarDataflow.v"
  "Phil.Systems scalar definition/use dataflow"
  "normalized typed-scalar definition/use sites with post-computed precedence"
  [ "verified_typed_scalar_has_exactly_one_definition"
  , "verified_scalar_use_has_unique_preceding_definition"
  , "missing_scalar_definition_is_rejected"
  , "multiple_scalar_definitions_are_rejected"
  , "non_dominating_scalar_definition_is_rejected"
  , "scalar_use_before_same_site_definition_is_rejected"
  ]
  "Concrete Data.Map/Data.Set enumeration, operation/terminator indexing, CFG reachability/dominance computation, and Text/ValueId correspondence remain implementation boundaries."
