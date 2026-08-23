{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqCoreControlAssurance
  ( coreControlAssuranceCertificationSpecs
  ) where

import qualified Data.Text
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types (ArtifactRef (..), EvidenceEntryId (..))
import Phil.Core.Syntax (ObligationId (..))

coreControlAssuranceCertificationSpecs :: [RocqCertificationSpec]
coreControlAssuranceCertificationSpecs =
  [ sessionRecSpec
  , processSeqSpec
  , processJoinSpec
  , processTerminalSpec
  , dischargeCertificateSpec
  , dischargeBoundarySpec
  , dischargePrerequisiteSpec
  , decisionLinearSpec
  ]

mkSpec
  :: String
  -> String
  -> String
  -> String
  -> String
  -> [String]
  -> String
  -> String
  -> String
  -> RocqCertificationSpec
mkSpec profile obligation claim kind source theorems scope representation residual =
  RocqCertificationSpec
    { rocqSpecProfile = fromString profile
    , rocqSpecObligation = ObligationId (fromString obligation)
    , rocqSpecClaim = fromString claim
    , rocqSpecKind = fromString kind
    , rocqSpecOrigin = fromString source
    , rocqSpecScope = fromString scope
    , rocqSpecRepresentation = fromString representation
    , rocqSpecSubjects = []
    , rocqSpecTheorems = map fromString theorems
    , rocqSpecSourceRef = ArtifactRef (fromString (proofPath source))
    , rocqSpecCompiledRef = ArtifactRef (fromString (objectPath source))
    , rocqSpecCertificateRef = ArtifactRef (fromString ("certificate:rocq:" <> obligation <> ":v1"))
    , rocqSpecEvidenceId = EvidenceEntryId (fromString ("evidence." <> obligation <> ".rocq.v1"))
    , rocqSpecResidualBoundary = fromString residual
    }
  where
    proofPath origin = afterSemicolon origin
    objectPath origin = replaceSuffix ".v" ".vo" (proofPath origin)

fromString :: String -> Data.Text.Text
fromString = Data.Text.pack

afterSemicolon :: String -> String
afterSemicolon value =
  case dropWhile (/= ';') value of
    [] -> value
    (_ : rest) -> dropWhile (== ' ') rest

replaceSuffix :: String -> String -> String -> String
replaceSuffix old new value
  | reverse old `prefixOf` reverse value = reverse (drop (length old) (reverse value)) <> new
  | otherwise = value <> new
  where
    prefixOf [] _ = True
    prefixOf _ [] = False
    prefixOf (x:xs) (y:ys) = x == y && prefixOf xs ys

sessionRecSpec :: RocqCertificationSpec
sessionRecSpec = mkSpec
  "core-session-recursion"
  "PHIL-SESSION-REC-001"
  "exposeSessionHead either exposes a non-recursive head after finite unfolding or rejects an unbound session variable / repeated unguarded recursion variable."
  "Core session-recursion termination and rejection"
  "src/Phil/Core/Session.hs::exposeSessionHead; proof/Phil/Core/SessionRec.v"
  [ "substitution_does_not_invent_recursion_names"
  , "exposure_step_names_subset"
  , "exposure_trace_invariants"
  , "initial_names_in_pool"
  , "exposure_trace_bounded"
  , "fuel_exhaustion_implies_trace"
  , "exposeSessionHeadModel_never_exhausts"
  , "exposed_result_is_nonrecursive_head"
  , "exposeSessionHeadModel_classifies"
  ]
  "Phil.Core.Session.exposeSessionHead finite seen-set semantics"
  "proof-oriented finite recursion-name pool and explicit derived fuel"
  "This certifies the implemented finite seen-set behavior, not a stronger global guardedness theorem. Message types remain opaque because exposeSessionHead does not inspect them; concrete Haskell Set/Text correspondence remains an implementation boundary."

processSeqSpec :: RocqCertificationSpec
processSeqSpec = mkSpec
  "core-process-sequence"
  "PHIL-PROC-SEQ-001"
  "sequenceFlow applies its continuation only to Continue paths; Return, Closed, and Failed paths are preserved unchanged."
  "Core process control-flow preservation"
  "src/Phil/Core/Process.hs::sequenceFlow; proof/Phil/Core/Process.v"
  [ "advance_continue_uses_continuation"
  , "advance_noncontinuing_preserved"
  , "sequenceFlow_preserves_noncontinuing"
  ]
  "Phil.Core.Process.sequenceFlow"
  "structural ProcessFlow model with opaque CheckState"
  "CheckState remains opaque; sequenceFlow is represented structurally rather than as mapM plus concatenation, with the same successful failure/order/multiplicity boundary. Concrete Haskell list traversal remains a correspondence boundary."

processJoinSpec :: RocqCertificationSpec
processJoinSpec = mkSpec
  "core-process-join"
  "PHIL-PROC-JOIN-001"
  "joinBranches joins only continuing resource contexts, preserves terminal paths, and normalizes every continuing path to the same joined context."
  "Core process branch convergence"
  "src/Phil/Core/Process.hs::joinBranches; proof/Phil/Core/ProcessJoin.v"
  [ "process_join_nonempty_branch_set"
  , "process_join_preserves_path_count"
  , "process_join_preserves_noncontinuing"
  , "process_join_normalizes_every_continue"
  ]
  "Phil.Core.Process.joinBranches"
  "proof-oriented flattened branch flow with opaque non-resource checker state"
  "The non-resource portion of CheckState remains opaque; path multiplicity/order and non-continuing path identity are modeled explicitly. Resource convergence relies on the separately certified ContextJoin boundary."

processTerminalSpec :: RocqCertificationSpec
processTerminalSpec = mkSpec
  "core-process-terminal"
  "PHIL-PROC-TERM-001"
  "Closed and Failed terminal flows are constructible only when the resource context has no active loans and no unconsumed linear resources."
  "Core terminal-state safety"
  "src/Phil/Core/Process.hs::{closedFlow,failedFlow}; proof/Phil/Core/ProcessTerminal.v"
  [ "terminal_flow_success_requires_resource_complete"
  , "terminal_flow_success_has_no_loans"
  , "terminal_flow_success_has_no_linear_resources"
  , "terminal_flow_never_returns"
  , "terminal_flow_never_continues"
  , "resource_complete_allows_closed"
  , "resource_complete_allows_failed"
  ]
  "Phil.Core.Process terminalFlow / ensureComplete"
  "extensional resource-completeness model"
  "Finite-map/set emptiness is represented extensionally. Return remains intentionally excluded because returnFlow checks ensureReturnable rather than full resource completeness."

dischargeCertificateSpec :: RocqCertificationSpec
dischargeCertificateSpec = mkSpec
  "core-discharge-certificate"
  "PHIL-DISCH-CERT-001"
  "A proposed decision certificate counts as static discharge only after the independent certificate checker accepts it; no proposal or a rejected certificate never constitutes proof."
  "Assurance producer/checker separation"
  "src/Phil/Core/Discharge.hs::resolveFocusedRequirement; proof/Phil/Core/Discharge.v"
  [ "static_certificate_requires_checker_acceptance"
  , "no_proposal_requires_explicit_mechanism"
  , "rejected_proposal_never_static"
  ]
  "Phil.Core.Discharge decision-certificate boundary"
  "proof-oriented producer/checker control boundary"
  "The theorem family establishes producer/checker control separation. Semantic soundness of accepted linear certificates is separately tracked by PHIL-DECISION-LINEAR-001."

dischargeBoundarySpec :: RocqCertificationSpec
dischargeBoundarySpec = mkSpec
  "core-discharge-boundary"
  "PHIL-DISCH-BOUNDARY-001"
  "A resolved obligation has only an explicit static discharge, an exact runtime binding, or an exact export binding; runtime/export identity, canonical proposition, and required point must match, and there is no implicit Assumed fallback."
  "Assurance disposition exactness"
  "src/Phil/Core/Discharge.hs::{resolveFocusedRequirement,resolveArchitecture,validateRuntimeBinding,validateExportBinding}; proof/Phil/Core/Discharge.v"
  [ "resolution_disposition_exact"
  , "runtime_resolution_requires_exact_identity"
  , "export_resolution_requires_exact_identity"
  ]
  "Phil.Core.Discharge disposition boundary"
  "normalized exact runtime/export binding model"
  "Canonicalization itself is treated as an established equality boundary. Artifact identity and ADR-010 manifest closure remain outside this checker-level theorem."

dischargePrerequisiteSpec :: RocqCertificationSpec
dischargePrerequisiteSpec = mkSpec
  "core-discharge-prerequisite"
  "PHIL-DISCH-PREREQ-001"
  "An exported prerequisite is not reused as a local solver assumption; if a parent depends on any exported prerequisite, the parent cannot be locally discharged and must itself cross an explicit export boundary."
  "Assurance export-boundary noninterference"
  "src/Phil/Core/Discharge.hs::{resolvePrerequisites,resolveFocusedRequirement,resolveExportOnly}; proof/Phil/Core/Discharge.v"
  [ "exported_prerequisite_is_not_local_assumption"
  , "local_prerequisite_becomes_assumption"
  , "exported_prerequisite_makes_allLocal_false"
  , "exported_prerequisite_blocks_local_parent"
  ]
  "Phil.Core.Discharge prerequisite resolution"
  "proof-oriented local/exported prerequisite disposition list"
  "Successful local prerequisite dispositions are abstracted; the theorem does not assert that an Exported proposition is true."

decisionLinearSpec :: RocqCertificationSpec
decisionLinearSpec = mkSpec
  "core-decision-linear"
  "PHIL-DECISION-LINEAR-001"
  "An accepted linear certificate denotes a valid linear consequence of its valid bases: equality goals use only equality bases with zero slack; inequality goals use inequality bases only at nonnegative weights and nonnegative slack; checked partial-operation prerequisites remain explicit assumptions."
  "Decision certificate semantic soundness"
  "src/Phil/Core/Decision.hs::{checkDecisionCertificate,checkLinearCertificate,basisPiece,basisRelation,ensurePartialOperationPrerequisites}; proof/Phil/Core/DecisionSound.v"
  [ "equality_term_is_zero"
  , "inequality_term_is_nonnegative"
  , "equality_weighted_sum_is_zero"
  , "inequality_weighted_sum_is_nonnegative"
  , "accepted_linear_certificate_is_sound"
  , "checked_certificate_requires_all_partial_prerequisites"
  , "checked_linear_certificate_semantically_sound"
  ]
  "Phil.Core.Decision linear-certificate checker"
  "rational affine denotation of checked linear certificates"
  "Correspondence from Haskell RefTerm normalization and sort checking to the proof-side affine denotation remains an explicit representation assumption. The certificate establishes checker soundness, not producer completeness."
