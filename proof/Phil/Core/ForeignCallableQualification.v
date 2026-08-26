From Stdlib Require Import Lists.List.

From Phil.Core Require Import CallableRefinement.

(*
  PHIL-CALL-FOREIGN-001 — explicit qualification of one exact foreign callable.

  Qualification binds evidence to one exact foreign artifact and one exact
  admitted semantic surface. Every independent evidence dimension is explicit.
  Successful qualification then remains subject to ordinary CALL-012 callable
  refinement; qualification never overrides semantic non-widening.
*)

Parameter ForeignArtifactKey EvidenceRef : Type.

Inductive ForeignEvidenceKind : Type :=
| EvidenceAbi
| EvidenceResourceLifecycle
| EvidenceEffectConfinement
| EvidenceAuthorityConfinement
| EvidenceFailureBehavior.

Record ForeignArtifact : Type := mkForeignArtifact {
  foreignArtifactKey : ForeignArtifactKey;
  foreignObservedSurface : CallableRefinementSurface
}.

Record ForeignQualification : Type := mkForeignQualification {
  qualificationArtifactKey : ForeignArtifactKey;
  qualificationSurface : CallableRefinementSurface;
  qualificationEvidence : ForeignEvidenceKind -> option EvidenceRef
}.

Definition CompleteForeignEvidence (qualification : ForeignQualification) : Prop :=
  forall kind, exists evidence,
    qualificationEvidence qualification kind = Some evidence.

Definition ForeignQualificationAccepts
  (expected : CallableRefinementSurface)
  (artifact : ForeignArtifact)
  (qualification : ForeignQualification) : Prop :=
  qualificationArtifactKey qualification = foreignArtifactKey artifact /\
  qualificationSurface qualification = foreignObservedSurface artifact /\
  CompleteForeignEvidence qualification /\
  callableRefines expected (qualificationSurface qualification).

Theorem accepted_qualification_is_bound_to_exact_artifact :
  forall expected artifact qualification,
    ForeignQualificationAccepts expected artifact qualification ->
    qualificationArtifactKey qualification = foreignArtifactKey artifact.
Proof.
  intros expected artifact qualification Haccepts.
  exact (proj1 Haccepts).
Qed.

Theorem cross_artifact_qualification_reuse_rejects :
  forall expected artifact qualification,
    qualificationArtifactKey qualification <> foreignArtifactKey artifact ->
    ~ ForeignQualificationAccepts expected artifact qualification.
Proof.
  intros expected artifact qualification Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 Haccepts).
Qed.

Theorem accepted_qualification_surface_is_exact :
  forall expected artifact qualification,
    ForeignQualificationAccepts expected artifact qualification ->
    qualificationSurface qualification = foreignObservedSurface artifact.
Proof.
  intros expected artifact qualification Haccepts.
  exact (proj1 (proj2 Haccepts)).
Qed.

Theorem qualification_surface_mismatch_rejects :
  forall expected artifact qualification,
    qualificationSurface qualification <> foreignObservedSurface artifact ->
    ~ ForeignQualificationAccepts expected artifact qualification.
Proof.
  intros expected artifact qualification Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 (proj2 Haccepts)).
Qed.

Theorem every_evidence_dimension_is_present :
  forall expected artifact qualification,
    ForeignQualificationAccepts expected artifact qualification ->
    (exists evidence, qualificationEvidence qualification EvidenceAbi = Some evidence) /\
    (exists evidence, qualificationEvidence qualification EvidenceResourceLifecycle = Some evidence) /\
    (exists evidence, qualificationEvidence qualification EvidenceEffectConfinement = Some evidence) /\
    (exists evidence, qualificationEvidence qualification EvidenceAuthorityConfinement = Some evidence) /\
    (exists evidence, qualificationEvidence qualification EvidenceFailureBehavior = Some evidence).
Proof.
  intros expected artifact qualification Haccepts.
  destruct Haccepts as [_ [_ [Hall _]]].
  repeat split; apply Hall.
Qed.

Theorem missing_any_evidence_dimension_rejects :
  forall expected artifact qualification kind,
    (forall evidence,
      qualificationEvidence qualification kind <> Some evidence) ->
    ~ ForeignQualificationAccepts expected artifact qualification.
Proof.
  intros expected artifact qualification kind Hmissing Haccepts.
  destruct Haccepts as [_ [_ [Hall _]]].
  destruct (Hall kind) as [evidence Hevidence].
  apply (Hmissing evidence).
  exact Hevidence.
Qed.

Theorem qualification_does_not_bypass_callable_refinement :
  forall expected artifact qualification,
    ForeignQualificationAccepts expected artifact qualification ->
    callableRefines expected (qualificationSurface qualification).
Proof.
  intros expected artifact qualification Haccepts.
  exact (proj2 (proj2 (proj2 Haccepts))).
Qed.

Theorem qualified_callable_never_strengthens_caller_authority :
  forall expected artifact qualification,
    ForeignQualificationAccepts expected artifact qualification ->
    setSubset
      (surfaceAuthority (qualificationSurface qualification))
      (surfaceAuthority expected).
Proof.
  intros expected artifact qualification Haccepts.
  apply refinement_never_strengthens_caller_authority.
  apply qualification_does_not_bypass_callable_refinement with (artifact := artifact).
  exact Haccepts.
Qed.

Theorem qualified_callable_never_widens_effects :
  forall expected artifact qualification,
    ForeignQualificationAccepts expected artifact qualification ->
    setSubset
      (surfaceEffects (qualificationSurface qualification))
      (surfaceEffects expected).
Proof.
  intros expected artifact qualification Haccepts.
  apply refinement_never_widens_effects.
  apply qualification_does_not_bypass_callable_refinement with (artifact := artifact).
  exact Haccepts.
Qed.

Theorem qualified_callable_never_adds_failures :
  forall expected artifact qualification,
    ForeignQualificationAccepts expected artifact qualification ->
    setSubset
      (surfaceFailures (qualificationSurface qualification))
      (surfaceFailures expected).
Proof.
  intros expected artifact qualification Haccepts.
  apply refinement_never_adds_failures.
  apply qualification_does_not_bypass_callable_refinement with (artifact := artifact).
  exact Haccepts.
Qed.

Theorem qualified_callable_preserves_callee_transition :
  forall expected artifact qualification,
    ForeignQualificationAccepts expected artifact qualification ->
    surfaceTransition (qualificationSurface qualification) =
    surfaceTransition expected.
Proof.
  intros expected artifact qualification Haccepts.
  apply refinement_requires_exact_callee_transition.
  apply qualification_does_not_bypass_callable_refinement with (artifact := artifact).
  exact Haccepts.
Qed.
