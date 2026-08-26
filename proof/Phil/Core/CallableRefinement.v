From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import CallableEffects CallableLifecycle.

(*
  PHIL-CALL-REFINE-001 — higher-order callable semantic refinement.

  Interface revision identity is intentionally carried separately from
  substitutability. A callable may be supplied where another callable is
  expected only when its machine-facing shape is equal, its caller-authority
  requirement is no stronger, its public may-effect and failure sets are no
  wider, and its callee lifecycle transition is exact.
*)

Definition BoolSet : Type := nat -> bool.

Definition setSubset (actual expected : BoolSet) : Prop :=
  forall element, actual element = true -> expected element = true.

Definition sameSet (first second : BoolSet) : Prop :=
  forall element, first element = second element.

Inductive RefinementTransition : Type :=
| PreserveTransition
| ConsumeTransition
| ReplaceTransition.

Record CallableRefinementSurface : Type := mkCallableRefinementSurface {
  surfaceInterfaceRevision : nat;
  surfaceMachineShape : nat;
  surfaceAuthority : BoolSet;
  surfaceEffects : BoolSet;
  surfaceFailures : BoolSet;
  surfaceTransition : RefinementTransition
}.

Definition callableRefines
  (expected actual : CallableRefinementSurface) : Prop :=
  surfaceMachineShape actual = surfaceMachineShape expected /\
  setSubset (surfaceAuthority actual) (surfaceAuthority expected) /\
  setSubset (surfaceEffects actual) (surfaceEffects expected) /\
  setSubset (surfaceFailures actual) (surfaceFailures expected) /\
  surfaceTransition actual = surfaceTransition expected.

Definition withInterfaceRevision
  (revision : nat)
  (surface : CallableRefinementSurface) : CallableRefinementSurface :=
  mkCallableRefinementSurface
    revision
    (surfaceMachineShape surface)
    (surfaceAuthority surface)
    (surfaceEffects surface)
    (surfaceFailures surface)
    (surfaceTransition surface).

Theorem set_subset_reflexive :
  forall effects, setSubset effects effects.
Proof.
  intros effects element Hpresent.
  exact Hpresent.
Qed.

Theorem set_subset_transitive :
  forall first second third,
    setSubset first second ->
    setSubset second third ->
    setSubset first third.
Proof.
  intros first second third Hfirst Hsecond element Hpresent.
  apply Hsecond.
  apply Hfirst.
  exact Hpresent.
Qed.

Theorem callable_refinement_is_reflexive :
  forall surface, callableRefines surface surface.
Proof.
  intros surface.
  unfold callableRefines.
  split.
  - reflexivity.
  - split.
    + apply set_subset_reflexive.
    + split.
      * apply set_subset_reflexive.
      * split.
        -- apply set_subset_reflexive.
        -- reflexivity.
Qed.

Theorem callable_refinement_is_transitive :
  forall expected middle actual,
    callableRefines expected middle ->
    callableRefines middle actual ->
    callableRefines expected actual.
Proof.
  intros expected middle actual Hfirst Hsecond.
  destruct Hfirst as [Hshape1 [Hauthority1 [Heffects1 [Hfailures1 Htransition1]]]].
  destruct Hsecond as [Hshape2 [Hauthority2 [Heffects2 [Hfailures2 Htransition2]]]].
  unfold callableRefines.
  split.
  - rewrite Hshape2. exact Hshape1.
  - split.
    + eapply set_subset_transitive; eauto.
    + split.
      * eapply set_subset_transitive; eauto.
      * split.
        -- eapply set_subset_transitive; eauto.
        -- rewrite Htransition2. exact Htransition1.
Qed.

Theorem refinement_preserves_machine_shape :
  forall expected actual,
    callableRefines expected actual ->
    surfaceMachineShape actual = surfaceMachineShape expected.
Proof.
  intros expected actual Hrefines.
  exact (proj1 Hrefines).
Qed.

Theorem refinement_never_strengthens_caller_authority :
  forall expected actual,
    callableRefines expected actual ->
    setSubset (surfaceAuthority actual) (surfaceAuthority expected).
Proof.
  intros expected actual Hrefines.
  exact (proj1 (proj2 Hrefines)).
Qed.

Theorem refinement_never_widens_effects :
  forall expected actual,
    callableRefines expected actual ->
    setSubset (surfaceEffects actual) (surfaceEffects expected).
Proof.
  intros expected actual Hrefines.
  exact (proj1 (proj2 (proj2 Hrefines))).
Qed.

Theorem refinement_never_adds_failures :
  forall expected actual,
    callableRefines expected actual ->
    setSubset (surfaceFailures actual) (surfaceFailures expected).
Proof.
  intros expected actual Hrefines.
  exact (proj1 (proj2 (proj2 (proj2 Hrefines)))).
Qed.

Theorem refinement_requires_exact_callee_transition :
  forall expected actual,
    callableRefines expected actual ->
    surfaceTransition actual = surfaceTransition expected.
Proof.
  intros expected actual Hrefines.
  exact (proj2 (proj2 (proj2 (proj2 Hrefines)))).
Qed.

Theorem distinct_interface_revisions_may_refine :
  forall expectedRevision actualRevision shape authority effects failures transition,
    callableRefines
      (mkCallableRefinementSurface
        expectedRevision shape authority effects failures transition)
      (mkCallableRefinementSurface
        actualRevision shape authority effects failures transition).
Proof.
  intros expectedRevision actualRevision shape authority effects failures transition.
  unfold callableRefines.
  cbn.
  split.
  - reflexivity.
  - split.
    + apply set_subset_reflexive.
    + split.
      * apply set_subset_reflexive.
      * split.
        -- apply set_subset_reflexive.
        -- reflexivity.
Qed.

Theorem interface_revision_is_noninterfering :
  forall expected actual expectedRevision actualRevision,
    callableRefines expected actual ->
    callableRefines
      (withInterfaceRevision expectedRevision expected)
      (withInterfaceRevision actualRevision actual).
Proof.
  intros expected actual expectedRevision actualRevision Hrefines.
  unfold callableRefines in *.
  cbn.
  exact Hrefines.
Qed.

Theorem narrower_actual_is_admissible :
  forall expectedRevision actualRevision shape
      expectedAuthority actualAuthority
      expectedEffects actualEffects
      expectedFailures actualFailures transition,
    setSubset actualAuthority expectedAuthority ->
    setSubset actualEffects expectedEffects ->
    setSubset actualFailures expectedFailures ->
    callableRefines
      (mkCallableRefinementSurface
        expectedRevision shape
        expectedAuthority expectedEffects expectedFailures transition)
      (mkCallableRefinementSurface
        actualRevision shape
        actualAuthority actualEffects actualFailures transition).
Proof.
  intros expectedRevision actualRevision shape
    expectedAuthority actualAuthority
    expectedEffects actualEffects
    expectedFailures actualFailures transition
    Hauthority Heffects Hfailures.
  unfold callableRefines.
  cbn.
  split.
  - reflexivity.
  - split.
    + exact Hauthority.
    + split.
      * exact Heffects.
      * split.
        -- exact Hfailures.
        -- reflexivity.
Qed.

Theorem stronger_authority_cannot_refine :
  forall expected actual witness,
    callableRefines expected actual ->
    surfaceAuthority actual witness = true ->
    surfaceAuthority expected witness = false ->
    False.
Proof.
  intros expected actual witness Hrefines Hactual Hexpected.
  pose proof (refinement_never_strengthens_caller_authority
    expected actual Hrefines witness Hactual) as Hallowed.
  rewrite Hexpected in Hallowed.
  discriminate.
Qed.

Theorem wider_effect_cannot_refine :
  forall expected actual witness,
    callableRefines expected actual ->
    surfaceEffects actual witness = true ->
    surfaceEffects expected witness = false ->
    False.
Proof.
  intros expected actual witness Hrefines Hactual Hexpected.
  pose proof (refinement_never_widens_effects
    expected actual Hrefines witness Hactual) as Hallowed.
  rewrite Hexpected in Hallowed.
  discriminate.
Qed.

Theorem extra_failure_cannot_refine :
  forall expected actual witness,
    callableRefines expected actual ->
    surfaceFailures actual witness = true ->
    surfaceFailures expected witness = false ->
    False.
Proof.
  intros expected actual witness Hrefines Hactual Hexpected.
  pose proof (refinement_never_adds_failures
    expected actual Hrefines witness Hactual) as Hallowed.
  rewrite Hexpected in Hallowed.
  discriminate.
Qed.

Theorem lifecycle_adaptation_is_never_implicit :
  forall expected actual,
    callableRefines expected actual ->
    surfaceTransition actual <> surfaceTransition expected ->
    False.
Proof.
  intros expected actual Hrefines Hdifferent.
  apply Hdifferent.
  apply refinement_requires_exact_callee_transition.
  exact Hrefines.
Qed.
