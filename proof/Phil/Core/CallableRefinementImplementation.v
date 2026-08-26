From Stdlib Require Import Bool.Bool Lists.List.

From Phil.Core Require Import CallableRefinement.

(*
  PHIL-ASSURE-IMPL-CORR-001 — CALL-012 implementation-refinement pilot.

  The existing PHIL-CALL-REFINE-001 theorem family deliberately abstracts
  concrete Haskell representation.  This file introduces the executable
  finite projection that the production checker can consume after a checked
  representation bridge.  The decision procedure is proved sound and complete
  for that exact projection, and the projection is proved to refine the
  existing CALL-012 semantic relation whenever its bridge obligations hold.

  The projection is intentionally finite.  Authority/effect/failure sets are
  represented as Boolean incidence vectors over a per-comparison finite domain.
  Machine-shape and full callee-transition equality are represented directly as
  Boolean facts.  In particular, the transition fact is stronger than the old
  Preserve/Consume/Replace-kind abstraction: production ReplaceCallee payload
  equality must already have been checked before this bit may be true.
*)

Definition BoolVector : Type := list bool.

Fixpoint vectorSubset (actual expected : BoolVector) : Prop :=
  match actual, expected with
  | nil, _ => True
  | true :: _, nil => False
  | false :: actualTail, nil => vectorSubset actualTail nil
  | true :: actualTail, true :: expectedTail =>
      vectorSubset actualTail expectedTail
  | true :: _, false :: _ => False
  | false :: actualTail, _ :: expectedTail =>
      vectorSubset actualTail expectedTail
  end.

Fixpoint vectorSubsetb (actual expected : BoolVector) : bool :=
  match actual, expected with
  | nil, _ => true
  | true :: _, nil => false
  | false :: actualTail, nil => vectorSubsetb actualTail nil
  | true :: actualTail, true :: expectedTail =>
      vectorSubsetb actualTail expectedTail
  | true :: _, false :: _ => false
  | false :: actualTail, _ :: expectedTail =>
      vectorSubsetb actualTail expectedTail
  end.

Theorem vector_subsetb_true_iff :
  forall actual expected,
    vectorSubsetb actual expected = true <-> vectorSubset actual expected.
Proof.
  induction actual as [| actualHead actualTail IH]; intros expected.
  - destruct expected; cbn; split; intro H.
    + exact I.
    + reflexivity.
    + exact I.
    + reflexivity.
  - destruct expected as [| expectedHead expectedTail].
    + destruct actualHead.
      * cbn. split; intro H.
        -- discriminate.
        -- contradiction.
      * cbn. apply IH.
    + destruct actualHead, expectedHead.
      * cbn. apply IH.
      * cbn. split; intro H.
        -- discriminate.
        -- contradiction.
      * cbn. apply IH.
      * cbn. apply IH.
Qed.

Inductive RefinementDecision : Type :=
| RefinementAccepted
| RefinementMachineShapeMismatch
| RefinementAuthorityTooStrong
| RefinementEffectsTooWide
| RefinementFailuresTooWide
| RefinementTransitionMismatch.

Record RefinementProjection : Type := mkRefinementProjection {
  projectionMachineShapeEqual : bool;
  projectionActualAuthority : BoolVector;
  projectionExpectedAuthority : BoolVector;
  projectionActualEffects : BoolVector;
  projectionExpectedEffects : BoolVector;
  projectionActualFailures : BoolVector;
  projectionExpectedFailures : BoolVector;
  projectionTransitionEqual : bool
}.

Definition implementationRefines
  (projection : RefinementProjection) : Prop :=
  projectionMachineShapeEqual projection = true /\
  vectorSubset
    (projectionActualAuthority projection)
    (projectionExpectedAuthority projection) /\
  vectorSubset
    (projectionActualEffects projection)
    (projectionExpectedEffects projection) /\
  vectorSubset
    (projectionActualFailures projection)
    (projectionExpectedFailures projection) /\
  projectionTransitionEqual projection = true.

Definition implementationRefinesb
  (projection : RefinementProjection) : bool :=
  projectionMachineShapeEqual projection &&
  vectorSubsetb
    (projectionActualAuthority projection)
    (projectionExpectedAuthority projection) &&
  vectorSubsetb
    (projectionActualEffects projection)
    (projectionExpectedEffects projection) &&
  vectorSubsetb
    (projectionActualFailures projection)
    (projectionExpectedFailures projection) &&
  projectionTransitionEqual projection.

Definition decideCallableRefinement
  (projection : RefinementProjection) : RefinementDecision :=
  if projectionMachineShapeEqual projection then
    if vectorSubsetb
        (projectionActualAuthority projection)
        (projectionExpectedAuthority projection) then
      if vectorSubsetb
          (projectionActualEffects projection)
          (projectionExpectedEffects projection) then
        if vectorSubsetb
            (projectionActualFailures projection)
            (projectionExpectedFailures projection) then
          if projectionTransitionEqual projection then
            RefinementAccepted
          else RefinementTransitionMismatch
        else RefinementFailuresTooWide
      else RefinementEffectsTooWide
    else RefinementAuthorityTooStrong
  else RefinementMachineShapeMismatch.

Definition decisionAcceptedb (decision : RefinementDecision) : bool :=
  match decision with
  | RefinementAccepted => true
  | _ => false
  end.

Theorem decision_acceptedb_true_iff :
  forall decision,
    decisionAcceptedb decision = true <-> decision = RefinementAccepted.
Proof.
  intros decision.
  destruct decision; cbn; split; intro H; try reflexivity; try discriminate.
Qed.

Theorem decision_acceptedb_matches_refinement_boolean :
  forall projection,
    decisionAcceptedb (decideCallableRefinement projection) =
      implementationRefinesb projection.
Proof.
  intros [shapeEqual
          actualAuthority expectedAuthority
          actualEffects expectedEffects
          actualFailures expectedFailures
          transitionEqual].
  unfold decisionAcceptedb, decideCallableRefinement, implementationRefinesb.
  cbn.
  destruct shapeEqual; cbn; try reflexivity.
  destruct (vectorSubsetb actualAuthority expectedAuthority); cbn; try reflexivity.
  destruct (vectorSubsetb actualEffects expectedEffects); cbn; try reflexivity.
  destruct (vectorSubsetb actualFailures expectedFailures); cbn; try reflexivity.
  destruct transitionEqual; reflexivity.
Qed.

Theorem implementation_refinesb_true_iff :
  forall projection,
    implementationRefinesb projection = true <-> implementationRefines projection.
Proof.
  intros projection.
  unfold implementationRefinesb, implementationRefines.
  repeat rewrite andb_true_iff.
  repeat rewrite vector_subsetb_true_iff.
  split.
  - intros [[[[Hshape Hauthority] Heffects] Hfailures] Htransition].
    split.
    + exact Hshape.
    + split.
      * exact Hauthority.
      * split.
        -- exact Heffects.
        -- split.
           ++ exact Hfailures.
           ++ exact Htransition.
  - intros [Hshape [Hauthority [Heffects [Hfailures Htransition]]]].
    split.
    + split.
      * split.
        -- split.
           ++ exact Hshape.
           ++ exact Hauthority.
        -- exact Heffects.
      * exact Hfailures.
    + exact Htransition.
Qed.

Theorem decision_accept_iff_implementation_refines :
  forall projection,
    decideCallableRefinement projection = RefinementAccepted <->
    implementationRefines projection.
Proof.
  intros projection.
  split.
  - intro Haccept.
    apply (proj1 (implementation_refinesb_true_iff projection)).
    rewrite <- decision_acceptedb_matches_refinement_boolean.
    rewrite Haccept.
    reflexivity.
  - intro Hrefines.
    apply (proj1 (decision_acceptedb_true_iff
      (decideCallableRefinement projection))).
    rewrite decision_acceptedb_matches_refinement_boolean.
    apply (proj2 (implementation_refinesb_true_iff projection)).
    exact Hrefines.
Qed.

Theorem decision_reject_iff_not_implementation_refines :
  forall projection,
    decideCallableRefinement projection <> RefinementAccepted <->
    ~ implementationRefines projection.
Proof.
  intros projection.
  split.
  - intros Hreject Hrefines.
    apply Hreject.
    apply (proj2 (decision_accept_iff_implementation_refines projection)).
    exact Hrefines.
  - intros Hnot Haccept.
    apply Hnot.
    apply (proj1 (decision_accept_iff_implementation_refines projection)).
    exact Haccept.
Qed.

(*
  Bridge theorem to the already-certified CALL-012 abstraction.

  The bridge premises are exactly the obligations of the concrete production
  projection layer.  The transition premise is one-way on purpose: the exact
  production equality includes ReplaceCallee payload identity, while the old
  abstraction records only transition kind.  Thus the implementation relation
  is allowed to be strictly stronger than CALL-012, never weaker.
*)
Theorem implementation_refinement_refines_call012 :
  forall projection expected actual,
    (projectionMachineShapeEqual projection = true ->
      surfaceMachineShape actual = surfaceMachineShape expected) ->
    (vectorSubset
        (projectionActualAuthority projection)
        (projectionExpectedAuthority projection) ->
      setSubset (surfaceAuthority actual) (surfaceAuthority expected)) ->
    (vectorSubset
        (projectionActualEffects projection)
        (projectionExpectedEffects projection) ->
      setSubset (surfaceEffects actual) (surfaceEffects expected)) ->
    (vectorSubset
        (projectionActualFailures projection)
        (projectionExpectedFailures projection) ->
      setSubset (surfaceFailures actual) (surfaceFailures expected)) ->
    (projectionTransitionEqual projection = true ->
      surfaceTransition actual = surfaceTransition expected) ->
    implementationRefines projection ->
    callableRefines expected actual.
Proof.
  intros projection expected actual
    Hshape Hauthority Heffects Hfailures Htransition Himplementation.
  destruct Himplementation as
    [HshapeBit [HauthorityBits [HeffectBits [HfailureBits HtransitionBit]]]].
  unfold callableRefines.
  split.
  - apply Hshape. exact HshapeBit.
  - split.
    + apply Hauthority. exact HauthorityBits.
    + split.
      * apply Heffects. exact HeffectBits.
      * split.
        -- apply Hfailures. exact HfailureBits.
        -- apply Htransition. exact HtransitionBit.
Qed.

Theorem accepted_implementation_projection_refines_call012 :
  forall projection expected actual,
    (projectionMachineShapeEqual projection = true ->
      surfaceMachineShape actual = surfaceMachineShape expected) ->
    (vectorSubset
        (projectionActualAuthority projection)
        (projectionExpectedAuthority projection) ->
      setSubset (surfaceAuthority actual) (surfaceAuthority expected)) ->
    (vectorSubset
        (projectionActualEffects projection)
        (projectionExpectedEffects projection) ->
      setSubset (surfaceEffects actual) (surfaceEffects expected)) ->
    (vectorSubset
        (projectionActualFailures projection)
        (projectionExpectedFailures projection) ->
      setSubset (surfaceFailures actual) (surfaceFailures expected)) ->
    (projectionTransitionEqual projection = true ->
      surfaceTransition actual = surfaceTransition expected) ->
    decideCallableRefinement projection = RefinementAccepted ->
    callableRefines expected actual.
Proof.
  intros projection expected actual
    Hshape Hauthority Heffects Hfailures Htransition Haccepted.
  apply implementation_refinement_refines_call012 with (projection := projection).
  - exact Hshape.
  - exact Hauthority.
  - exact Heffects.
  - exact Hfailures.
  - exact Htransition.
  - apply (proj1 (decision_accept_iff_implementation_refines projection)).
    exact Haccepted.
Qed.
