{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqAssuranceFoundations
  ( assuranceFoundationCertificationSpecs
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types (ArtifactRef (..), EvidenceEntryId (..))
import Phil.Core.Syntax (ObligationId (..))

assuranceFoundationCertificationSpecs :: [RocqCertificationSpec]
assuranceFoundationCertificationSpecs =
  [ scopeSpec
  , acceptanceSpec
  , graphSpec
  , assumptionSpec
  , evidenceSpec
  , useSpec
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

scopeSpec :: RocqCertificationSpec
scopeSpec = mkSpec
  "assurance-scope"
  "PHIL-ASSURE-SCOPE-001"
  "A verified manifest covers exactly the trusted expected obligation-revision set. Certification scope is a subset of that set; every in-scope revision must be locally accepted and cannot be exported; every out-of-scope revision must have exactly one explicit export to a permitted boundary; evidence may not use an exported obligation as a truth-producing dependency."
  "Assurance certification-scope closure"
  "src/Phil/Assurance/Verify.hs::{verifyManifestSets,verifyExport,verifyDependencies,verifyObligationClosure}; proof/Phil/Assurance/Manifest.v"
  "proof/Phil/Assurance/Manifest.v"
  "Phil.Assurance manifest scope closure"
  "extensional revision/evidence/boundary sets"
  [ "verified_manifest_covers_exact_trusted_revision_set"
  , "certification_scope_is_inside_manifest"
  , "in_scope_revision_is_locally_accepted"
  , "in_scope_revision_is_not_exported"
  , "out_of_scope_manifest_revision_has_permitted_export"
  , "out_of_scope_export_is_unique"
  , "selected_evidence_cannot_depend_on_exported_revision_as_truth"
  ]
  "Manifest/scope membership is modeled extensionally. Concrete Set ordering, identifier/digest correspondence, and diagnostic constructors remain implementation boundaries."

acceptanceSpec :: RocqCertificationSpec
acceptanceSpec = mkSpec
  "assurance-acceptance"
  "PHIL-ASSURE-ACCEPT-001"
  "An in-scope obligation is accepted only by a structurally non-vacuous acceptance rule whose required entries are satisfied by selected evidence for the exact revision, assurance kind, and role; candidate evidence must itself be accepted and all of its evidence/obligation dependencies recursively usable. Missing or rejected evidence never satisfies a rule."
  "Assurance non-vacuous evidence acceptance"
  "src/Phil/Assurance/Verify.hs::{validAcceptanceRule,obligationAccepted,evaluateRule,evidenceUsable,dependencyUsable}; proof/Phil/Assurance/Manifest.v"
  "proof/Phil/Assurance/Manifest.v"
  "Phil.Assurance evidence-acceptance algebra"
  "validated nonempty acceptance-rule trees and extensional evidence environment"
  [ "empty_all_acceptance_rule_is_rejected"
  , "empty_any_acceptance_rule_is_rejected"
  , "accepted_entry_requires_selected_exact_usable_evidence"
  , "accepted_all_requires_both_children"
  , "accepted_any_requires_one_child"
  , "matching_evidence_is_selected"
  , "matching_evidence_is_accepted"
  , "matching_evidence_has_usable_dependencies"
  , "rejected_evidence_cannot_match"
  , "unselected_evidence_cannot_match"
  ]
  "Validated nonempty Haskell AcceptAll/AcceptAny lists are normalized to proof-side binary trees. Exact list-to-tree/container correspondence and semantic truth of external artifacts remain explicit boundaries."

graphSpec :: RocqCertificationSpec
graphSpec = mkSpec
  "assurance-graph"
  "PHIL-ASSURE-GRAPH-001"
  "The selected justification graph is acyclic across obligation-to-evidence edges, evidence dependencies, obligation dependencies, and revision-lineage edges; any detected cycle rejects the manifest, and recursive evidence/obligation usability never turns a revisited node into successful justification."
  "Assurance justification acyclicity"
  "src/Phil/Assurance/Verify.hs::{graphEdges,findCycle,evidenceUsable,obligationAccepted}; proof/Phil/Assurance/Manifest.v"
  "proof/Phil/Assurance/Manifest.v"
  "Phil.Assurance justification graph"
  "normalized obligation/evidence graph and visiting-set guard"
  [ "verified_graph_has_no_self_edge"
  , "verified_graph_has_no_two_node_cycle"
  , "revisited_node_is_never_entered_as_justification"
  , "successful_visit_implies_node_was_not_already_visiting"
  ]
  "Protocol/session recursion is outside this graph. Concrete graph extraction from Maps/Sets and identifier correspondence remain implementation boundaries."

assumptionSpec :: RocqCertificationSpec
assumptionSpec = mkSpec
  "assurance-assumption-authority"
  "PHIL-ASSURE-ASSUME-001"
  "An assumption can contribute to selected evidence only when its stable identity and content digest verify, it is explicitly selected by the manifest, explicitly permitted by the verification context, and valid for the effective target/profile/context; evidence of kind Assumed additionally requires a nonempty explicit assumption boundary."
  "Assurance explicit assumption authority"
  "src/Phil/Assurance/Verify.hs::{verifyEvidenceAssumption,verifyAssumption,verifyAssumed}; proof/Phil/Assurance/EvidenceUse.v"
  "proof/Phil/Assurance/EvidenceUse.v"
  "Phil.Assurance assumption/evidence authority gates"
  "normalized exact-match assumption authority booleans"
  [ "successful_assumption_authority_is_exact"
  , "successful_assumed_evidence_has_explicit_authority_boundary"
  , "unpermitted_assumption_cannot_contribute_authority"
  , "stale_assumption_scope_cannot_contribute_authority"
  ]
  "Digest collision resistance is a cryptographic assumption; this theorem establishes verifier gating on exact identities/digests and explicit authority, not SHA-256 injectivity or assumption truth."

evidenceSpec :: RocqCertificationSpec
evidenceSpec = mkSpec
  "assurance-evidence-kind-authority"
  "PHIL-ASSURE-EVID-001"
  "Evidence kinds carry explicit checker obligations: proof-assistant, certificate, translation-validation, differential-test, and property-test evidence require the exact declared artifact/digest in the trusted availability context; RuntimeEnforced evidence requires a complete mechanism, nonempty runtime residue, and known ADR-011 cost reference; no kind silently upgrades incomplete evidence."
  "Assurance evidence-kind authority"
  "src/Phil/Assurance/Verify.hs::{verifyArtifact,verifyKindRequirements,verifyRuntime,verifyCostRef}; proof/Phil/Assurance/EvidenceUse.v"
  "proof/Phil/Assurance/EvidenceUse.v"
  "Phil.Assurance evidence-kind authority gates"
  "normalized artifact/runtime/assumption authority model"
  [ "successful_artifact_authority_is_exact"
  , "successful_runtime_authority_is_complete"
  , "artifact_backed_kind_cannot_upgrade_incomplete_artifact"
  , "runtime_kind_acceptance_requires_complete_runtime_authority"
  , "assumed_kind_acceptance_requires_explicit_assumption_authority"
  ]
  "The verifier checks exact artifact identity/digest availability but does not rerun external proof assistants, tests, or translation validators. Those tools and artifact semantics remain declared trust boundaries."

useSpec :: RocqCertificationSpec
useSpec = mkSpec
  "assurance-use-exactness"
  "PHIL-ASSURE-USE-001"
  "A verified assurance use applies only to an accepted in-scope revision: erasure requires at least one usable evidence entry for that exact revision; retained-runtime use requires usable RuntimeEnforced evidence for that exact revision and the same known cost reference. Existing ledger revisions/evidence/assumptions/exports/uses are append-only and cannot be rewritten in place."
  "Assurance-use exactness and immutable history"
  "src/Phil/Assurance/Verify.hs::{verifyUse,verifyUseEvidence,verifyLedgerExtension}; proof/Phil/Assurance/EvidenceUse.v"
  "proof/Phil/Assurance/EvidenceUse.v"
  "Phil.Assurance use and one-step ledger-extension gates"
  "normalized exact-revision use evidence and structural ledger maps"
  [ "verified_erasure_use_is_nonempty_and_exact"
  , "verified_runtime_use_is_exact_runtime_evidence_with_known_cost"
  , "non_runtime_evidence_cannot_authorize_retained_runtime_use"
  , "verified_ledger_extension_preserves_every_existing_node"
  , "verified_ledger_extension_forbids_in_place_rewrite"
  ]
  "Content addressing/digest checks and concrete Map/Set correspondence remain implementation boundaries. Append-only semantics are structural equality of existing nodes, not cryptographic injectivity; multi-step composition is separately certified by PHIL-ASSURE-LEDGER-EXT-001."
