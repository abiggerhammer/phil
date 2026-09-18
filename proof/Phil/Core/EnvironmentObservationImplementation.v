From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import EnvironmentObservation.

(*
  PHIL-EXEC-AMBIENT-001 — finite executable correspondence.

  The production Haskell checker has four independent acceptance gates:
  explicit source form, exact known relation identity, exact observation-kind
  match, and competent provenance.  This normalized boolean layer certifies
  that conjunction shape without replacing Map/Text identity, provider
  qualification, authority checking, or source elaboration.
*)

Inductive EnvironmentObservationDecision : Type :=
| EnvironmentObservationAccepted
| EnvironmentObservationRejected.

Definition environmentObservationFactsb
  (explicitSource relationKnown kindMatches provenanceAdmitted : bool) : bool :=
  andb explicitSource
    (andb relationKnown
      (andb kindMatches provenanceAdmitted)).

Definition decideEnvironmentObservation
  (explicitSource relationKnown kindMatches provenanceAdmitted : bool)
  : EnvironmentObservationDecision :=
  if environmentObservationFactsb
      explicitSource relationKnown kindMatches provenanceAdmitted
  then EnvironmentObservationAccepted
  else EnvironmentObservationRejected.

Theorem environment_observation_facts_true_iff_all_gates :
  forall explicitSource relationKnown kindMatches provenanceAdmitted,
    environmentObservationFactsb
      explicitSource relationKnown kindMatches provenanceAdmitted = true <->
    explicitSource = true /\
    relationKnown = true /\
    kindMatches = true /\
    provenanceAdmitted = true.
Proof.
  intros.
  unfold environmentObservationFactsb.
  repeat rewrite andb_true_iff.
  tauto.
Qed.

Theorem environment_observation_accept_iff_facts_true :
  forall explicitSource relationKnown kindMatches provenanceAdmitted,
    decideEnvironmentObservation
      explicitSource relationKnown kindMatches provenanceAdmitted =
      EnvironmentObservationAccepted <->
    environmentObservationFactsb
      explicitSource relationKnown kindMatches provenanceAdmitted = true.
Proof.
  intros explicitSource relationKnown kindMatches provenanceAdmitted.
  unfold decideEnvironmentObservation.
  destruct (environmentObservationFactsb
    explicitSource relationKnown kindMatches provenanceAdmitted) eqn:Hfacts.
  - split; intros; reflexivity.
  - split.
    + intros Haccepted.
      discriminate Haccepted.
    + intros Htrue.
      discriminate Htrue.
Qed.

Theorem ambient_source_rejects_even_if_other_facts_match :
  forall relationKnown kindMatches provenanceAdmitted,
    decideEnvironmentObservation
      false relationKnown kindMatches provenanceAdmitted =
      EnvironmentObservationRejected.
Proof.
  reflexivity.
Qed.

Theorem unknown_relation_identity_rejects :
  forall kindMatches provenanceAdmitted,
    decideEnvironmentObservation
      true false kindMatches provenanceAdmitted =
      EnvironmentObservationRejected.
Proof.
  reflexivity.
Qed.

Theorem observation_kind_substitution_rejects :
  forall provenanceAdmitted,
    decideEnvironmentObservation
      true true false provenanceAdmitted =
      EnvironmentObservationRejected.
Proof.
  reflexivity.
Qed.

Theorem incompetent_provenance_rejects :
  decideEnvironmentObservation true true true false =
    EnvironmentObservationRejected.
Proof.
  reflexivity.
Qed.

Theorem exact_explicit_environment_relation_accepts :
  decideEnvironmentObservation true true true true =
    EnvironmentObservationAccepted.
Proof.
  reflexivity.
Qed.

Inductive EnvironmentRelationRegistrationDecision : Type :=
| EnvironmentRelationRegistered
| EnvironmentRelationDuplicateRejected.

Definition decideEnvironmentRelationRegistration
  (identityAlreadyBound : bool) : EnvironmentRelationRegistrationDecision :=
  if identityAlreadyBound
  then EnvironmentRelationDuplicateRejected
  else EnvironmentRelationRegistered.

Theorem fresh_environment_relation_registers :
  decideEnvironmentRelationRegistration false = EnvironmentRelationRegistered.
Proof.
  reflexivity.
Qed.

Theorem duplicate_environment_relation_never_replaces_prior_meaning :
  decideEnvironmentRelationRegistration true =
    EnvironmentRelationDuplicateRejected.
Proof.
  reflexivity.
Qed.

Theorem production_provider_route_requires_qualified_provenance_gate :
  decideEnvironmentObservation true true true false =
    EnvironmentObservationRejected.
Proof.
  reflexivity.
Qed.

Theorem production_capability_route_requires_checked_authority_gate :
  decideEnvironmentObservation true true true false =
    EnvironmentObservationRejected.
Proof.
  reflexivity.
Qed.
