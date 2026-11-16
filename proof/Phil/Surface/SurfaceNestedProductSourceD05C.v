From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context DataProduct.
From Phil.Surface Require Import
  SurfaceNestedProductFoundationD05A SurfaceNestedProductSurfaceD05B.

(*
  FSEM-01 DATA-05C: the conditional source-owned two-level product adapter
  model. Source binders, exact leaf types and a globally fresh intermediate
  are premises established by the real Haskell source checker/production
  Surface tests; this is NOT a general Haskell↔Rocq refinement claim.
*)
Module D := DataProduct.
Module C := Context.
Module B := SurfaceNestedProductSurfaceD05B.
Module A := SurfaceNestedProductFoundationD05A.

Inductive NestedSide : Type :=
| NestedLeft
| NestedRight.

Record CheckedNestedSourcePlan : Type := {
  sourcePacketOwner : Name;
  sourceInnerOwner : Name;
  sourceFlagOwner : Name;
  sourceBytesOwner : Name;
  sourceUnitOwner : Name;
  sourceSide : NestedSide;
  sourceOuterMembers : list D.ProductElementContract;
  sourceInnerMembers : list D.ProductElementContract
}.

Definition sourceOuterNames (plan : CheckedNestedSourcePlan)
  : list Name :=
  match sourceSide plan with
  | NestedLeft => [sourceInnerOwner plan; sourceFlagOwner plan]
  | NestedRight => [sourceFlagOwner plan; sourceInnerOwner plan]
  end.

Definition sourceInnerNames (plan : CheckedNestedSourcePlan)
  : list Name :=
  [sourceBytesOwner plan; sourceUnitOwner plan].

Definition SourceBinderFreshness (plan : CheckedNestedSourcePlan) : Prop :=
  NoDup [sourcePacketOwner plan;
         sourceInnerOwner plan;
         sourceFlagOwner plan;
         sourceBytesOwner plan;
         sourceUnitOwner plan].

Definition SourceNestedProductAccepted (plan : CheckedNestedSourcePlan) : Prop :=
  SourceBinderFreshness plan /\
  D.ProductEliminationAccepted
    (sourceOuterMembers plan) (sourceOuterNames plan) /\
  D.ProductEliminationAccepted
    (sourceInnerMembers plan) (sourceInnerNames plan).

Definition replaySourceNested (plan : CheckedNestedSourcePlan) :=
  B.replayTwoStages
    (sourceOuterMembers plan) (sourceInnerMembers plan)
    (sourceOuterNames plan) (sourceInnerNames plan).

Theorem data05c_checked_source_has_two_replayable_stages :
  forall plan,
    SourceNestedProductAccepted plan ->
    exists first second,
      replaySourceNested plan = Some (first,second) /\
      NoDup (sourceOuterNames plan) /\
      NoDup (sourceInnerNames plan).
Proof.
  intros plan [_ [Houter Hinner]].
  unfold replaySourceNested.
  eapply B.data05b_accepted_two_stage_plan_replays.
  - exact Houter.
  - exact Hinner.
Qed.

Theorem data05c_source_missing_outer_plan_has_no_successor :
  forall plan,
    D.productRestorationPlan
      (sourceOuterMembers plan) (sourceOuterNames plan) = None ->
    replaySourceNested plan = None.
Proof.
  intros plan H.
  unfold replaySourceNested.
  now apply B.data05b_missing_first_restoration_has_no_second_successor.
Qed.

Theorem data05c_source_missing_inner_plan_has_no_successor :
  forall plan,
    D.productRestorationPlan
      (sourceInnerMembers plan) (sourceInnerNames plan) = None ->
    replaySourceNested plan = None.
Proof.
  intros plan H.
  unfold replaySourceNested, B.replayTwoStages.
  destruct (D.productRestorationPlan
    (sourceOuterMembers plan) (sourceOuterNames plan))
    as [outerPlan|]; [now rewrite H|reflexivity].
Qed.

Theorem data05c_source_replay_preserves_exact_inner_leaf :
  forall plan first second index leaf owner,
    replaySourceNested plan = Some (first,second) ->
    nth_error (sourceInnerMembers plan) index = Some leaf ->
    nth_error (sourceInnerNames plan) index = Some owner ->
    nth_error second index = Some
      (D.mkRestoredProductBinding owner
        (D.productElementMode leaf) (D.productElementType leaf)).
Proof.
  intros plan first second index leaf owner Hreplay Hleaf Howner.
  unfold replaySourceNested in Hreplay.
  eapply B.data05b_successful_pair_has_no_fabricated_inner_leaf; eauto.
Qed.

Theorem data05c_distinct_source_and_intermediate_owner_not_resurrected :
  forall plan initial afterOuter afterInner outerTy innerTy,
    C.consumeLinear (sourcePacketOwner plan) initial =
      C.Consumed outerTy afterOuter ->
    C.consumeLinear (sourceInnerOwner plan) afterOuter =
      C.Consumed innerTy afterInner ->
    SourceBinderFreshness plan ->
    C.linearBindings afterInner (sourcePacketOwner plan) = None /\
    C.linearBindings afterInner (sourceInnerOwner plan) = None.
Proof.
  intros plan initial afterOuter afterInner outerTy innerTy
    Houter Hinner Hfresh.
  eapply A.data05a_two_linear_moves_do_not_resurrect_owners; eauto.
  unfold SourceBinderFreshness in Hfresh.
  inversion Hfresh as [|packet tail Hnotin Hnodup]; subst.
  simpl in Hnotin.
  apply String.eqb_neq.
  intro Heq.
  apply Hnotin.
  left.
  symmetry.
  exact Heq.
Qed.

Print Assumptions data05c_checked_source_has_two_replayable_stages.
Print Assumptions data05c_source_missing_outer_plan_has_no_successor.
Print Assumptions data05c_source_missing_inner_plan_has_no_successor.
Print Assumptions data05c_source_replay_preserves_exact_inner_leaf.
Print Assumptions data05c_distinct_source_and_intermediate_owner_not_resurrected.
