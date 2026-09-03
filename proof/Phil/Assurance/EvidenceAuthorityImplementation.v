From Stdlib Require Import Bool.Bool.
From Phil.Assurance Require Import EvidenceUse.

(*
  PHIL-ASSURE-EVID-001 implementation-refinement staging.

  The Certified EvidenceUse model already contains executable artifact-backed
  and RuntimeEnforced authority gates.  This file exposes only flat Boolean
  wrappers suitable for extraction and proves their acceptance bits are exactly
  the Certified conjunctions.  Concrete artifact lookup/digest comparison,
  runtime-mechanism construction, residue/cost-reference enumeration, and
  diagnostic reconstruction remain native correspondence boundaries.

  Assumed evidence is intentionally not part of this slice; its authority is
  owned by the separate explicit-assumption boundary in EvidenceUse.v.
*)

Definition artifactAuthorityFacts
  (declared identityMatches digestMatches : bool) : bool :=
  andb declared (andb identityMatches digestMatches).

Definition runtimeAuthorityFacts
  (mechanismPresent mechanismComplete residuePresent
   costReferencePresent costReferenceKnown : bool) : bool :=
  andb mechanismPresent
    (andb mechanismComplete
      (andb residuePresent
        (andb costReferencePresent costReferenceKnown))).

Definition decideArtifactAuthorityByFacts
  (declared identityMatches digestMatches : bool) : GateResult :=
  verifyArtifactAuthority
    (mkArtifactAuthority declared identityMatches digestMatches).

Definition decideRuntimeAuthorityByFacts
  (mechanismPresent mechanismComplete residuePresent
   costReferencePresent costReferenceKnown : bool) : GateResult :=
  verifyRuntimeAuthority
    (mkRuntimeAuthority
      mechanismPresent
      mechanismComplete
      residuePresent
      costReferencePresent
      costReferenceKnown).

Definition gateResultAccepts (result : GateResult) : bool :=
  match result with
  | GateRejected => false
  | GateAccepted => true
  end.

Theorem artifact_authority_decision_is_certified_gate :
  forall declared identityMatches digestMatches,
    decideArtifactAuthorityByFacts declared identityMatches digestMatches =
    verifyArtifactAuthority
      (mkArtifactAuthority declared identityMatches digestMatches).
Proof.
  reflexivity.
Qed.

Theorem runtime_authority_decision_is_certified_gate :
  forall mechanismPresent mechanismComplete residuePresent
         costReferencePresent costReferenceKnown,
    decideRuntimeAuthorityByFacts
      mechanismPresent mechanismComplete residuePresent
      costReferencePresent costReferenceKnown =
    verifyRuntimeAuthority
      (mkRuntimeAuthority
        mechanismPresent mechanismComplete residuePresent
        costReferencePresent costReferenceKnown).
Proof.
  reflexivity.
Qed.

Theorem artifact_authority_acceptance_reflects_exact_facts :
  forall declared identityMatches digestMatches,
    gateResultAccepts
      (decideArtifactAuthorityByFacts
        declared identityMatches digestMatches) =
    artifactAuthorityFacts declared identityMatches digestMatches.
Proof.
  destruct declared, identityMatches, digestMatches; reflexivity.
Qed.

Theorem runtime_authority_acceptance_reflects_exact_facts :
  forall mechanismPresent mechanismComplete residuePresent
         costReferencePresent costReferenceKnown,
    gateResultAccepts
      (decideRuntimeAuthorityByFacts
        mechanismPresent mechanismComplete residuePresent
        costReferencePresent costReferenceKnown) =
    runtimeAuthorityFacts
      mechanismPresent mechanismComplete residuePresent
      costReferencePresent costReferenceKnown.
Proof.
  destruct mechanismPresent, mechanismComplete, residuePresent,
    costReferencePresent, costReferenceKnown; reflexivity.
Qed.

Theorem exact_artifact_authority_facts_accept :
  decideArtifactAuthorityByFacts true true true = GateAccepted.
Proof.
  reflexivity.
Qed.

Theorem exact_runtime_authority_facts_accept :
  decideRuntimeAuthorityByFacts true true true true true = GateAccepted.
Proof.
  reflexivity.
Qed.
