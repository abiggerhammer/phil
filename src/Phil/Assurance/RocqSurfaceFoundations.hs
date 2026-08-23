{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqSurfaceFoundations
  ( surfaceFoundationCertificationSpecs
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types (ArtifactRef (..), EvidenceEntryId (..))
import Phil.Core.Syntax (ObligationId (..))

surfaceFoundationCertificationSpecs :: [RocqCertificationSpec]
surfaceFoundationCertificationSpecs =
  [ elaborationSpec
  , failureSpec
  , architectureSpec
  , controlSpec
  , scopeJoinSpec
  , freshOwnershipSpec
  , systemsProjectionSpec
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

elaborationSpec :: RocqCertificationSpec
elaborationSpec = mkSpec
  "surface-elaboration"
  "PHIL-SURFACE-ELAB-001"
  "Every supported surface refinement/type/value form elaborates to its designated existing Core constructor, with proposition normalization and dependent Nat-index coercion delegated to the proved focusing boundary rather than inventing new semantics."
  "Surface canonical elaboration"
  "src/Phil/Surface/Elaborate.hs; proof/Phil/Surface/Elaboration.v"
  "proof/Phil/Surface/Elaboration.v"
  "Phil.Surface supported elaboration competence"
  "normalized surface/Core refinement, proposition, type, and value syntax with explicit focusing services"
  [ "variable_elaborates_exactly"
  , "boolean_elaborates_exactly"
  , "addition_elaborates_exactly"
  , "field_elaboration_uses_exact_declared_projection_sort"
  , "literal_left_multiplication_is_exact_scale"
  , "proposition_elaboration_delegates_exact_canonicalization"
  , "greater_than_has_designated_core_orientation"
  , "bytes_type_delegates_exact_nat_index_elaboration"
  , "proof_type_uses_exact_canonical_proposition"
  , "validated_type_preserves_exact_identities"
  , "expected_uint_literal_elaborates_exact_width"
  , "refined_expected_uint_literal_preserves_base_width"
  ]
  "The parsed Surface AST is taken as input. Proposition canonicalization and dependent Nat-index elaboration are explicit focusing-boundary services; concrete opaque Text rendering and Haskell constructor correspondence remain representation assumptions."

failureSpec :: RocqCertificationSpec
failureSpec = mkSpec
  "surface-elaboration-failure"
  "PHIL-SURFACE-FAIL-001"
  "Surface elaboration never guesses proof-relevant information: unknown projection sorts, symbolic multiplication outside the Phase 0 refinement fragment, ambiguous integer widths, non-name validation identities, and unsupported opaque type-index syntax reject explicitly."
  "Surface fail-closed elaboration"
  "src/Phil/Surface/Elaborate.hs; proof/Phil/Surface/Elaboration.v"
  "proof/Phil/Surface/Elaboration.v"
  "Phil.Surface fail-closed elaboration competence"
  "normalized rejection boundary for proof-relevant missing/unsupported information"
  [ "unknown_projection_sort_rejects"
  , "symbolic_multiplication_rejects"
  , "non_name_validation_context_rejects"
  , "non_name_validation_subject_rejects"
  , "unsupported_opaque_argument_prevents_rendering"
  , "unsupported_opaque_type_argument_rejects"
  , "ambiguous_integer_literal_rejects"
  ]
  "Error source-span precision remains an implementation/test property. The theorem targets absence of successful guessed Core results rather than concrete diagnostic rendering."

architectureSpec :: RocqCertificationSpec
architectureSpec = mkSpec
  "surface-architecture-agreement"
  "PHIL-SURFACE-ARCH-001"
  "Architecture-supplied initial bindings cannot be overridden by source annotations: a typed source parameter reusing an architecture binding succeeds only when resolved structural mode and Core type definitionally agree; an untyped source parameter requires an architecture binding; named surface type aliases resolve only through the explicit architecture alias map."
  "Surface architecture agreement"
  "src/Phil/Surface/Check/Engine.hs; src/Phil/Surface/Check/Support.hs; proof/Phil/Surface/Checking.v"
  "proof/Phil/Surface/Checking.v"
  "Phil.Surface whole-component architecture/type agreement"
  "normalized architecture binding and alias environment"
  [ "typed_parameter_cannot_override_architecture"
  , "untyped_parameter_preserves_architecture"
  , "untyped_parameter_requires_architecture"
  , "typed_parameter_without_architecture_is_exact_source_binding"
  , "explicit_alias_resolves_exactly"
  , "absent_alias_remains_opaque"
  , "nondefault_named_resolution_requires_explicit_alias"
  ]
  "The proof models the architecture/type-agreement competence boundary; concrete Text/Map lookup and Core compareTypes correspondence remain representation assumptions unless separately tightened."

controlSpec :: RocqCertificationSpec
controlSpec = mkSpec
  "surface-control"
  "PHIL-SURFACE-CTRL-001"
  "Surface sequencing advances only continuing paths: Return, Closed, and Failed paths are never re-entered as continuing computation, and a source-explicit statement after an unconditional return/close/fail is rejected as ControlAfterTerminal rather than silently skipped."
  "Surface terminal-control monotonicity"
  "src/Phil/Surface/Check/Preflight.hs; src/Phil/Surface/Check/Engine.hs; proof/Phil/Surface/Checking.v"
  "proof/Phil/Surface/Checking.v"
  "Phil.Surface terminal-control sequencing/preflight"
  "normalized path-control and statement-list model"
  [ "noncontinuing_control_is_never_reentered"
  , "terminal_control_cannot_become_continue"
  , "terminal_path_survives_surface_sequence"
  , "terminal_head_with_following_statement_rejects"
  , "successful_terminal_head_has_no_following_statement"
  , "successful_nonterminal_prefix_delegates_to_tail"
  ]
  "Expression semantics are abstracted to path-control results and syntactically unconditional terminal forms. Dynamic branch feasibility remains an input to ordinary checker execution."

scopeJoinSpec :: RocqCertificationSpec
scopeJoinSpec = mkSpec
  "surface-scope-join"
  "PHIL-SURFACE-SCOPE-001"
  "A continuing branch cannot leak branch-local authority or ownership: live local linear bindings reject scope exit; discardable locals are removed before rejoin; successful continuing-path joins preserve only Core resource residue common under join semantics and require surviving surface metadata to agree across branches."
  "Surface branch-local scope and join"
  "src/Phil/Surface/Check/Engine.hs; src/Phil/Core/Context.hs::joinContinuing; proof/Phil/Surface/ScopeJoin.v"
  "proof/Phil/Surface/ScopeJoin.v"
  "Phil.Surface scope pruning and metadata join around Core convergence"
  "extensional surface metadata maps over certified Core context-join semantics"
  [ "successful_scope_exit_has_no_live_local_linear"
  , "successful_scope_exit_removes_every_local_binding"
  , "successful_scope_exit_preserves_incoming_binding"
  , "joined_metadata_is_first_branch_core_survivor"
  , "joined_metadata_agrees_across_continuing_branches"
  , "non_surviving_core_binding_is_absent_from_joined_metadata"
  , "successful_surface_join_preserves_core_linear_convergence"
  , "successful_surface_join_preserves_core_unrestricted_convergence"
  ]
  "Scope pruning and metadata agreement are modeled extensionally; concrete Map ordering and exact diagnostic text remain implementation-level properties. Core convergence is separately certified."

freshOwnershipSpec :: RocqCertificationSpec
freshOwnershipSpec = mkSpec
  "surface-fresh-ownership"
  "PHIL-SURFACE-FRESH-001"
  "Successful surface session progression never duplicates endpoint ownership: the old programmer-visible linear endpoint is consumed in Core, the Core session operation installs a fresh temporary successor owner, that temporary owner is extracted exactly once, and only then may the surface layer bind/rebind the programmer-visible successor name."
  "Surface fresh successor ownership"
  "src/Phil/Surface/Check/Support.hs; src/Phil/Surface/Check/Engine.hs; src/Phil/Core/Session.hs; proof/Phil/Surface/FreshOwnership.v"
  "proof/Phil/Surface/FreshOwnership.v"
  "Phil.Surface/Core successor-owner bridge"
  "three-phase Core synthetic-owner extraction and surface rebind model"
  [ "surface_progress_rebind_success_exact"
  , "successful_surface_rebind_requires_final_name_freshness"
  , "successful_surface_rebind_has_no_intermediate_duplicate_owner"
  ]
  "The theorem proves actual Core ownership freshness from successful insertion; concrete fresh-name generation and reserved synthetic-name namespace separation remain implementation correspondence assumptions."

systemsProjectionSpec :: RocqCertificationSpec
systemsProjectionSpec = mkSpec
  "surface-systems-projection"
  "PHIL-SURF-SYS-PROJ-001"
  "For the runnable scalar fragment, independent Surface -> Systems projection validation preserves the contextual scalar type, each source named literal's exact value identity and literal, alias identity, and returned-value semantics; it rejects source-literal drift, target type drift, wrong variable-return targets, direct-return literal drift, and invented scalar definitions."
  "Surface to Systems translation validation"
  "src/Phil/Compiler.hs; proof/Phil/Surface/SystemsProjection.v"
  "proof/Phil/Surface/SystemsProjection.v"
  "runnable scalar Surface-to-Systems projection validation"
  "normalized contextual scalar source judgment and target scalar definitions/return"
  [ "verified_projection_has_runnable_source_judgment"
  , "verified_named_literal_preserves_identity_type_and_value"
  , "verified_target_scalar_has_contextual_type"
  , "verified_target_definition_has_scalar_value_entry"
  , "verified_surface_alias_reuses_value_identity"
  , "verified_variable_return_preserves_exact_identity"
  , "verified_direct_literal_return_preserves_exact_value"
  , "verified_variable_return_has_no_invented_scalar_definition"
  , "source_literal_drift_is_rejected"
  , "scalar_type_drift_is_rejected"
  , "variable_return_target_drift_is_rejected"
  , "direct_literal_return_value_drift_is_rejected"
  , "invented_definition_on_variable_return_is_rejected"
  ]
  "Concrete Surface parsing/checking, runnable-fragment contextual U32 judgment correspondence, Text/ValueId mapping, Data.Map duplicate normalization, and Haskell-to-normalized-model correspondence remain implementation boundaries."
