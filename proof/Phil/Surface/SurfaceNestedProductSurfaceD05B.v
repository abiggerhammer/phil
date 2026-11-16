From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax DataProduct.
From Phil.Surface Require Import SurfaceNestedProductFoundationD05A.

(*
  FSEM-01 DATA-05B: bounded two-stage flat projection, with explicit
  conditional source/type/owner premises. These theorems do NOT assert that
  production Haskell has been refined by this model; native Haskell tests
  execute both actual Surface transitions and compare to independent Core.
*)
Module D := DataProduct.
Module A := SurfaceNestedProductFoundationD05A.

Definition replayTwoStages
    (outerElements innerElements : list D.ProductElementContract)
    (outerNames innerNames : list Syntax.Name)
    : option (list D.RestoredProductBinding *
              list D.RestoredProductBinding) :=
  match D.productRestorationPlan outerElements outerNames with
  | None => None
  | Some outerRestored =>
      match D.productRestorationPlan innerElements innerNames with
      | None => None
      | Some innerRestored => Some (outerRestored,innerRestored)
      end
  end.

Theorem data05b_missing_first_restoration_has_no_second_successor :
  forall outer inner outerNames innerNames,
    D.productRestorationPlan outer outerNames = None ->
    replayTwoStages outer inner outerNames innerNames = None.
Proof.
  intros outer inner outerNames innerNames H.
  unfold replayTwoStages.
  now rewrite H.
Qed.

Theorem data05b_missing_second_restoration_has_no_successor :
  forall outer inner outerNames innerNames first,
    D.productRestorationPlan outer outerNames = Some first ->
    D.productRestorationPlan inner innerNames = None ->
    replayTwoStages outer inner outerNames innerNames = None.
Proof.
  intros outer inner outerNames innerNames first Hfirst Hsecond.
  unfold replayTwoStages.
  now rewrite Hfirst,Hsecond.
Qed.

Theorem data05b_successful_pair_preserves_both_arity_contracts :
  forall outer inner outerNames innerNames first second,
    replayTwoStages outer inner outerNames innerNames =
      Some (first,second) ->
    List.length outer = List.length outerNames /\
    List.length inner = List.length innerNames.
Proof.
  intros outer inner outerNames innerNames first second H.
  unfold replayTwoStages in H.
  destruct (D.productRestorationPlan outer outerNames) as [outerPlan|]
    eqn:Houter; try discriminate.
  destruct (D.productRestorationPlan inner innerNames) as [innerPlan|]
    eqn:Hinner; try discriminate.
  inversion H; subst; clear H.
  split.
  - exact (proj1 (D.restoration_plan_success_has_exact_lengths
      outer outerNames first Houter)).
  - exact (proj1 (D.restoration_plan_success_has_exact_lengths
      inner innerNames second Hinner)).
Qed.

Theorem data05b_successful_pair_has_no_fabricated_inner_leaf :
  forall outer inner outerNames innerNames first second index leaf owner,
    replayTwoStages outer inner outerNames innerNames =
      Some (first,second) ->
    nth_error inner index = Some leaf ->
    nth_error innerNames index = Some owner ->
    nth_error second index = Some
      (D.mkRestoredProductBinding owner
        (D.productElementMode leaf) (D.productElementType leaf)).
Proof.
  intros outer inner outerNames innerNames first second index leaf owner
    H Hleaf Howner.
  unfold replayTwoStages in H.
  destruct (D.productRestorationPlan outer outerNames) as [outerPlan|]
    eqn:Houter; try discriminate.
  destruct (D.productRestorationPlan inner innerNames) as [innerPlan|]
    eqn:Hinner; try discriminate.
  inversion H; subst; clear H.
  eapply D.restoration_plan_preserves_exact_element_contract; eauto.
Qed.

Theorem data05b_accepted_two_stage_plan_replays :
  forall outer inner outerNames innerNames,
    D.ProductEliminationAccepted outer outerNames ->
    D.ProductEliminationAccepted inner innerNames ->
    exists first second,
      replayTwoStages outer inner outerNames innerNames = Some (first,second) /\
      NoDup outerNames /\ NoDup innerNames.
Proof.
  intros outer inner outerNames innerNames Houter Hinner.
  destruct Houter as [first [Hfirst Hnames1]].
  destruct Hinner as [second [Hsecond Hnames2]].
  exists first,second.
  unfold replayTwoStages.
  rewrite Hfirst,Hsecond.
  repeat split; assumption || reflexivity.
Qed.

Print Assumptions data05b_missing_first_restoration_has_no_second_successor.
Print Assumptions data05b_missing_second_restoration_has_no_successor.
Print Assumptions data05b_successful_pair_preserves_both_arity_contracts.
Print Assumptions data05b_successful_pair_has_no_fabricated_inner_leaf.
Print Assumptions data05b_accepted_two_stage_plan_replays.
