From Phil.Core Require Import CallableRefinement.

(*
  PHIL-CALL-LOWER-001 — target callable representation preservation.

  Representation choice and representation identity are deliberately absent
  from the acceptance predicate. Every source semantic coordinate is preserved
  exactly, while every target-introduced realization consequence is accounted
  exactly by the accepted StageContract-side accounting record.
*)

Parameter CallableOccurrence StructuralMode CaptureSummary InternalAuthority LoanSet : Type.
Parameter TargetRepresentation RepresentationIdentity ConsequenceSet CostShape : Type.

Record SourceCallableLowering : Type := mkSourceCallableLowering {
  sourceLoweringSurface : CallableRefinementSurface;
  sourceLoweringOccurrence : CallableOccurrence;
  sourceLoweringMode : StructuralMode;
  sourceLoweringCaptures : CaptureSummary;
  sourceLoweringInternalAuthority : InternalAuthority;
  sourceLoweringLoans : LoanSet
}.

Record TargetCallableLowering : Type := mkTargetCallableLowering {
  targetRepresentation : TargetRepresentation;
  targetRepresentationIdentity : RepresentationIdentity;
  targetLoweringSurface : CallableRefinementSurface;
  targetLoweringOccurrence : CallableOccurrence;
  targetLoweringMode : StructuralMode;
  targetLoweringCaptures : CaptureSummary;
  targetLoweringInternalAuthority : InternalAuthority;
  targetLoweringLoans : LoanSet;
  targetIntroducedEffects : ConsequenceSet;
  targetIntroducedFailures : ConsequenceSet;
  targetIntroducedAssumptions : ConsequenceSet;
  targetIntroducedCarriers : ConsequenceSet;
  targetIntroducedCost : CostShape
}.

Record CallableRealizationAccounting : Type := mkCallableRealizationAccounting {
  accountedEffects : ConsequenceSet;
  accountedFailures : ConsequenceSet;
  accountedAssumptions : ConsequenceSet;
  accountedCarriers : ConsequenceSet;
  accountedCost : CostShape
}.

Definition CallableLoweringAccepts
  (source : SourceCallableLowering)
  (target : TargetCallableLowering)
  (accounting : CallableRealizationAccounting) : Prop :=
  targetLoweringSurface target = sourceLoweringSurface source /\
  targetLoweringOccurrence target = sourceLoweringOccurrence source /\
  targetLoweringMode target = sourceLoweringMode source /\
  targetLoweringCaptures target = sourceLoweringCaptures source /\
  targetLoweringInternalAuthority target = sourceLoweringInternalAuthority source /\
  targetLoweringLoans target = sourceLoweringLoans source /\
  accountedEffects accounting = targetIntroducedEffects target /\
  accountedFailures accounting = targetIntroducedFailures target /\
  accountedAssumptions accounting = targetIntroducedAssumptions target /\
  accountedCarriers accounting = targetIntroducedCarriers target /\
  accountedCost accounting = targetIntroducedCost target.

Definition withRepresentation
  (representation : TargetRepresentation)
  (identity : RepresentationIdentity)
  (target : TargetCallableLowering) : TargetCallableLowering :=
  mkTargetCallableLowering
    representation
    identity
    (targetLoweringSurface target)
    (targetLoweringOccurrence target)
    (targetLoweringMode target)
    (targetLoweringCaptures target)
    (targetLoweringInternalAuthority target)
    (targetLoweringLoans target)
    (targetIntroducedEffects target)
    (targetIntroducedFailures target)
    (targetIntroducedAssumptions target)
    (targetIntroducedCarriers target)
    (targetIntroducedCost target).

Theorem accepted_lowering_preserves_complete_source_projection :
  forall source target accounting,
    CallableLoweringAccepts source target accounting ->
    targetLoweringSurface target = sourceLoweringSurface source /\
    targetLoweringOccurrence target = sourceLoweringOccurrence source /\
    targetLoweringMode target = sourceLoweringMode source /\
    targetLoweringCaptures target = sourceLoweringCaptures source /\
    targetLoweringInternalAuthority target = sourceLoweringInternalAuthority source /\
    targetLoweringLoans target = sourceLoweringLoans source.
Proof.
  intros source target accounting Haccepts.
  destruct Haccepts as [Hsurface [Hoccurrence [Hmode [Hcaptures [Hauthority [Hloans Haccounting]]]]]].
  repeat split; assumption.
Qed.

Theorem accepted_lowering_accounts_every_introduced_consequence_exactly :
  forall source target accounting,
    CallableLoweringAccepts source target accounting ->
    accountedEffects accounting = targetIntroducedEffects target /\
    accountedFailures accounting = targetIntroducedFailures target /\
    accountedAssumptions accounting = targetIntroducedAssumptions target /\
    accountedCarriers accounting = targetIntroducedCarriers target /\
    accountedCost accounting = targetIntroducedCost target.
Proof.
  intros source target accounting Haccepts.
  destruct Haccepts as [_ [_ [_ [_ [_ [_ Haccounting]]]]]].
  exact Haccounting.
Qed.

Theorem representation_choice_is_nonsemantic :
  forall source target accounting representation identity,
    CallableLoweringAccepts source target accounting ->
    CallableLoweringAccepts
      source
      (withRepresentation representation identity target)
      accounting.
Proof.
  intros source target accounting representation identity Haccepts.
  unfold CallableLoweringAccepts in *.
  simpl.
  exact Haccepts.
Qed.

Theorem representation_identity_cannot_repair_surface_mismatch :
  forall source target accounting,
    targetLoweringSurface target <> sourceLoweringSurface source ->
    ~ CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 Haccepts).
Qed.

Theorem representation_identity_cannot_repair_occurrence_mismatch :
  forall source target accounting,
    targetLoweringOccurrence target <> sourceLoweringOccurrence source ->
    ~ CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 (proj2 Haccepts)).
Qed.

Theorem representation_identity_cannot_repair_capture_mismatch :
  forall source target accounting,
    targetLoweringCaptures target <> sourceLoweringCaptures source ->
    ~ CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 (proj2 (proj2 (proj2 Haccepts)))).
Qed.

Theorem representation_identity_cannot_repair_loan_mismatch :
  forall source target accounting,
    targetLoweringLoans target <> sourceLoweringLoans source ->
    ~ CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Haccepts)))))).
Qed.

Theorem unaccounted_effect_rejects :
  forall source target accounting,
    accountedEffects accounting <> targetIntroducedEffects target ->
    ~ CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Haccepts))))))).
Qed.

Theorem unaccounted_failure_rejects :
  forall source target accounting,
    accountedFailures accounting <> targetIntroducedFailures target ->
    ~ CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Haccepts)))))))).
Qed.

Theorem unaccounted_assumption_rejects :
  forall source target accounting,
    accountedAssumptions accounting <> targetIntroducedAssumptions target ->
    ~ CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Haccepts))))))))).
Qed.

Theorem unaccounted_carrier_rejects :
  forall source target accounting,
    accountedCarriers accounting <> targetIntroducedCarriers target ->
    ~ CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Haccepts)))))))))).
Qed.

Theorem unaccounted_cost_rejects :
  forall source target accounting,
    accountedCost accounting <> targetIntroducedCost target ->
    ~ CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting Hmismatch Haccepts.
  apply Hmismatch.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Haccepts)))))))))).
Qed.
