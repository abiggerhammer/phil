{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqFocusingFoundations
  ( focusingFoundationCertificationSpecs
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types (ArtifactRef (..), EvidenceEntryId (..))
import Phil.Core.Syntax (ObligationId (..))

focusingFoundationCertificationSpecs :: [RocqCertificationSpec]
focusingFoundationCertificationSpecs =
  [ coercionSpec
  , claimSpec
  , prerequisiteSpec
  , mechanismSpec
  , branchSpec
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

coercionSpec :: RocqCertificationSpec
coercionSpec = mkSpec
  "focusing-coercion"
  "PHIL-FOCUS-COERCE-001"
  "Focusing inserts exactly the canonical UInt[w] -> Nat coercion when a Nat context receives a UInt term, preserves already-matching sorts unchanged, and never inserts an implicit Nat -> UInt[w] coercion."
  "Focusing canonical coercion"
  "src/Phil/Core/Focusing.hs; proof/Phil/Core/Focusing.v"
  "proof/Phil/Core/Focusing.v"
  "Phil.Core.Focusing canonical coercion competence"
  "proof-oriented refinement-sort and coercion relation"
  [ "elaborate_matching_sort_is_identity"
  , "elaborate_uint_as_nat_is_exact"
  , "elaborate_nat_as_uint_rejects"
  ]
  "The proof models refinement sorts and the coercion competence relation directly; concrete Haskell sort inference remains the input/correspondence boundary."

claimSpec :: RocqCertificationSpec
claimSpec = mkSpec
  "focusing-claim"
  "PHIL-FOCUS-CLAIM-001"
  "Transparent claims expand by declared parameter substitution before normalization; opaque claims remain opaque atoms; unknown, arity/sort-invalid, free-variable, or recursively transparent definitions reject rather than being guessed or silently accepted."
  "Focusing claim expansion and rejection"
  "src/Phil/Core/Focusing.hs; src/Phil/Core/Static.hs; proof/Phil/Core/Focusing.v"
  "proof/Phil/Core/Focusing.v"
  "Phil.Core.Focusing claim expansion competence"
  "normalized transparent/opaque claim environment and expansion-stack discipline"
  [ "unknown_claim_rejects"
  , "invalid_claim_arguments_reject"
  , "opaque_claim_preserves_declared_identity"
  , "transparent_claim_expands_exact_declared_body"
  , "recursive_transparent_claim_rejects"
  , "ill_scoped_transparent_claim_rejects"
  ]
  "The proof targets focusing competence and expansion-stack discipline. Concrete Map lookup/order and full substitution implementation remain representation correspondence assumptions."

prerequisiteSpec :: RocqCertificationSpec
prerequisiteSpec = mkSpec
  "focusing-prerequisite"
  "PHIL-FOCUS-PREREQ-001"
  "Side conditions introduced by partial refinement operations are recursively focused and surfaced as explicit prerequisites before main-goal normalization; a normalization that simplifies the parent goal cannot erase those prerequisites."
  "Focusing prerequisite preservation"
  "src/Phil/Core/Focusing.hs; src/Phil/Core/SortCheck.hs::propositionSideConditions; proof/Phil/Core/Focusing.v"
  "proof/Phil/Core/Focusing.v"
  "Phil.Core.Focusing side-goal/prerequisite assembly"
  "deterministic side-condition extraction with canonical-key deduplication"
  [ "side_goal_survives_deduplicated_assembly"
  , "nested_side_prerequisite_survives_deduplicated_assembly"
  ]
  "The side-condition extractor and proposition normalizer are abstract deterministic functions; the theorem proves ordering/preservation in the focus-plan construction rather than their concrete implementation."

mechanismSpec :: RocqCertificationSpec
mechanismSpec = mkSpec
  "focusing-mechanism"
  "PHIL-FOCUS-MECH-001"
  "After canonicalization and prerequisite focusing, Truth is definitionally discharged; matching unrestricted evidence is preferred; Falsehood rejects; unresolved propositions containing an opaque claim require an explicit mechanism; every other unresolved transparent proposition stops at the decision-procedure boundary."
  "Focusing authority and mechanism classification"
  "src/Phil/Core/Focusing.hs; proof/Phil/Core/Focusing.v"
  "proof/Phil/Core/Focusing.v"
  "Phil.Core.Focusing closed mechanism-classification precedence"
  "normalized canonical-goal and evidence-match classification model"
  [ "truth_is_definitionally_discharged"
  , "matching_evidence_precedes_later_boundaries"
  , "falsehood_without_evidence_rejects"
  , "unresolved_opaque_goal_needs_explicit_mechanism"
  , "unresolved_transparent_goal_stops_at_decision_boundary"
  ]
  "Evidence search is modeled by an abstract canonical-match predicate; the theorem proves classification precedence and absence of any authority-generating fallback."

branchSpec :: RocqCertificationSpec
branchSpec = mkSpec
  "focusing-branch"
  "PHIL-FOCUS-BRANCH-001"
  "Branch exhaustiveness succeeds iff declared labels and handler labels are duplicate-free and denote the same label set; duplicates reject first, and mismatches report exactly the missing and extra labels."
  "Focusing branch exhaustiveness"
  "src/Phil/Core/Focusing.hs::checkBranchExhaustiveness; proof/Phil/Core/Focusing.v"
  "proof/Phil/Core/Focusing.v"
  "Phil.Core.Focusing duplicate-free exact branch coverage"
  "proof-oriented structural label membership/set equality"
  [ "successful_branch_check_is_exact"
  , "duplicate_declared_label_prevents_success"
  , "duplicate_handler_label_prevents_success"
  , "missing_handler_prevents_success"
  , "extra_handler_prevents_success"
  , "exact_duplicate_free_coverage_is_success"
  ]
  "The proof uses extensional list membership/set equality rather than Data.Set ordering; exact diagnostic-list ordering remains an implementation-level tested property."
