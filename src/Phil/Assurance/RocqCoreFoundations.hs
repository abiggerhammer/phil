{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqCoreFoundations
  ( coreFoundationCertificationSpecs
  ) where

import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types (ArtifactRef (..), EvidenceEntryId (..))
import Phil.Core.Syntax (ObligationId (..))

coreFoundationCertificationSpecs :: [RocqCertificationSpec]
coreFoundationCertificationSpecs =
  [ contextBindingSpec
  , contextLinearSpec
  , contextJoinSpec
  , sessionDualSpec
  , sessionStepSpec
  , sessionLabelSpec
  ]

contextBindingSpec :: RocqCertificationSpec
contextBindingSpec = RocqCertificationSpec
  { rocqSpecProfile = "core-context-binding"
  , rocqSpecObligation = ObligationId "PHIL-CTX-BIND-001"
  , rocqSpecClaim =
      "A successful insertBinding requires the name to be absent from all three structural binding maps, installs it in exactly the selected mode, preserves every unrelated lookup, and leaves the active-loan set unchanged."
  , rocqSpecKind = "Core context binding invariant"
  , rocqSpecOrigin = "src/Phil/Core/Context.hs::insertBinding; proof/Phil/Core/Context.v"
  , rocqSpecScope = "Phil.Core.Context.insertBinding successful-result semantics"
  , rocqSpecRepresentation = "extensional binding-map and loan-set model"
  , rocqSpecSubjects = ["ResourceContext", "insertBinding", "binding maps", "active loans"]
  , rocqSpecTheorems =
      [ "insertBinding_success_exact"
      , "insertBinding_success_name_was_fresh"
      , "insertBinding_success_preserves_other_names"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/Context.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/Context.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CTX-BIND-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CTX-BIND-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from Haskell finite Data.Map/Data.Set operations to the extensional binding-map/loan-set proof model remain explicit trust boundaries. The theorem family concerns successful insertion and does not certify diagnostic text or concrete finite-map representation."
  }

contextLinearSpec :: RocqCertificationSpec
contextLinearSpec = RocqCertificationSpec
  { rocqSpecProfile = "core-context-linear"
  , rocqSpecObligation = ObligationId "PHIL-CTX-LIN-001"
  , rocqSpecClaim =
      "A successful consumeLinear removes exactly the requested linear binding and leaves every other binding and active-loan entry unchanged."
  , rocqSpecKind = "Core linear-resource preservation"
  , rocqSpecOrigin = "src/Phil/Core/Context.hs::consumeLinear; proof/Phil/Core/Context.v"
  , rocqSpecScope = "Phil.Core.Context.consumeLinear successful-result semantics"
  , rocqSpecRepresentation = "extensional linear-binding map and loan-set model"
  , rocqSpecSubjects = ["ResourceContext", "consumeLinear", "linear bindings", "active loans"]
  , rocqSpecTheorems =
      [ "consumeLinear_success_exact"
      , "consumeLinear_success_consumes_owner"
      , "consumeLinear_success_preserves_other_linear"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/Context.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/Context.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CTX-LIN-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CTX-LIN-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from Haskell finite-map/set lookup, deletion, and loan checks to the extensional proof model remain explicit trust boundaries. Error classification outside the successful-result premise is not established by this theorem family."
  }

contextJoinSpec :: RocqCertificationSpec
contextJoinSpec = RocqCertificationSpec
  { rocqSpecProfile = "core-context-join"
  , rocqSpecObligation = ObligationId "PHIL-CTX-JOIN-001"
  , rocqSpecClaim =
      "A successful joinContinuing has identical unrestricted and linear bindings across all continuing branches, no escaping loans, and retains only affine bindings common to all branches at the same type."
  , rocqSpecKind = "Core branch-context convergence"
  , rocqSpecOrigin = "src/Phil/Core/Context.hs::joinContinuing; proof/Phil/Core/ContextJoin.v"
  , rocqSpecScope = "Phil.Core.Context.joinContinuing successful branch convergence"
  , rocqSpecRepresentation = "extensional branch contexts with proof-oriented affine left-fold intersection"
  , rocqSpecSubjects = ["ResourceContext", "joinContinuing", "unrestricted bindings", "linear bindings", "affine intersection", "loans"]
  , rocqSpecTheorems =
      [ "context_join_inputs_have_no_loans"
      , "context_join_output_has_no_loans"
      , "context_join_unrestricted_converges"
      , "context_join_linear_converges"
      , "context_join_affine_some_exact"
      , "context_join_affine_retained_is_common"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ContextJoin.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ContextJoin.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CTX-JOIN-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CTX-JOIN-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from Haskell branch enumeration, finite maps/sets, and left-fold affine intersection to the extensional proof model remain explicit trust boundaries. Concrete Map ordering and diagnostics are not certified."
  }

sessionDualSpec :: RocqCertificationSpec
sessionDualSpec = RocqCertificationSpec
  { rocqSpecProfile = "core-session-dual"
  , rocqSpecObligation = ObligationId "PHIL-SESSION-DUAL-001"
  , rocqSpecClaim = "For every session S, dualSession (dualSession S) = S."
  , rocqSpecKind = "Core session duality algebra"
  , rocqSpecOrigin = "src/Phil/Core/Session.hs::dualSession; proof/Phil/Core/Session.v"
  , rocqSpecScope = "Phil.Core.Session dualSession / dualBranches"
  , rocqSpecRepresentation = "proof-side mutually inductive Session/Branches syntax"
  , rocqSpecSubjects = ["Session", "Branches", "dualSession", "dualBranches"]
  , rocqSpecTheorems = ["dual_involutive", "dualSession_involutive"]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/Session.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/Session.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SESSION-DUAL-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SESSION-DUAL-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence between Haskell Session syntax and the proof-side mutually inductive Session/Branches representation remain explicit trust boundaries. Message types are opaque because duality preserves them unchanged."
  }

sessionStepSpec :: RocqCertificationSpec
sessionStepSpec = RocqCertificationSpec
  { rocqSpecProfile = "core-session-step"
  , rocqSpecObligation = ObligationId "PHIL-SESSION-STEP-001"
  , rocqSpecClaim =
      "Successful non-close session progression consumes the old linear endpoint, rejects endpoint-name reuse, installs a fresh linear successor carrying the continuation, and preserves unrelated linear lookups and loans; close consumes the endpoint with no successor while preserving unrelated linear lookups and loans."
  , rocqSpecKind = "Core session-step resource preservation"
  , rocqSpecOrigin = "src/Phil/Core/Session.hs::{sendEndpoint,receiveEndpoint,selectEndpoint,offerEndpoint,closeEndpoint}; proof/Phil/Core/SessionStep.v"
  , rocqSpecScope = "resource effects of successful Core session progression"
  , rocqSpecRepresentation = "endpoint resource transition over extensional ResourceContext"
  , rocqSpecSubjects = ["linear endpoint", "continuation endpoint", "ResourceContext", "active loans"]
  , rocqSpecTheorems =
      [ "continueEndpointResource_success_exact"
      , "closeEndpointResource_success_exact"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/SessionStep.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/SessionStep.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SESSION-STEP-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SESSION-STEP-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from Haskell session operations and TyEndpoint representation to the proof-side resource transition remain explicit trust boundaries. Session-head/action matching is outside this resource theorem."
  }

sessionLabelSpec :: RocqCertificationSpec
sessionLabelSpec = RocqCertificationSpec
  { rocqSpecProfile = "core-session-label"
  , rocqSpecObligation = ObligationId "PHIL-SESSION-LABEL-001"
  , rocqSpecClaim =
      "Successful Select/Offer progression chooses exactly one branch with the requested label; duplicate labels and absent labels are rejected before continuation."
  , rocqSpecKind = "Core session-label determinism and rejection"
  , rocqSpecOrigin = "src/Phil/Core/Session.hs::{selectBranch,ensureUniqueLabels}; proof/Phil/Core/SessionLabel.v"
  , rocqSpecScope = "Phil.Core.Session branch-label selection"
  , rocqSpecRepresentation = "proof-oriented branch spine with structural label counting/uniqueness"
  , rocqSpecSubjects = ["Branches", "selectBranch", "branch labels", "payload", "continuation"]
  , rocqSpecTheorems =
      [ "selectBranch_success_exactly_one"
      , "selectBranch_success_returns_requested_lookup"
      , "selectBranch_duplicate_labels_rejected"
      , "selectBranch_absent_label_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/SessionLabel.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/SessionLabel.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SESSION-LABEL-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SESSION-LABEL-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from Haskell Data.Set duplicate rejection and branch lookup to the proof-side structural branch spine remain explicit trust boundaries. Exact diagnostic-list ordering is not certified."
  }
