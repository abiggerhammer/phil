From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax DataProduct.

(*
  FSEM-01 DATA-04/05D: conditional source-owned three-stage product plan.
  Source identity/type premises are independently tested in production
  Haskell/Core/Surface. NOT a universal Haskell-to-Rocq refinement theorem.
*)
Module D := DataProduct.

Definition replayThreeStages
    (outer middle deep : list D.ProductElementContract)
    (outerNames middleNames deepNames : list Syntax.Name)
    : option (list D.RestoredProductBinding *
              list D.RestoredProductBinding *
              list D.RestoredProductBinding) :=
  match D.productRestorationPlan outer outerNames with
  | None => None
  | Some restoredOuter =>
      match D.productRestorationPlan middle middleNames with
      | None => None
      | Some restoredMiddle =>
          match D.productRestorationPlan deep deepNames with
          | None => None
          | Some restoredDeep =>
              Some (restoredOuter,restoredMiddle,restoredDeep)
          end
      end
  end.

Theorem data05d_checked_three_stage_plan_replays :
  forall outer middle deep outerNames middleNames deepNames,
    D.ProductEliminationAccepted outer outerNames ->
    D.ProductEliminationAccepted middle middleNames ->
    D.ProductEliminationAccepted deep deepNames ->
    exists first second third,
      replayThreeStages outer middle deep outerNames middleNames deepNames =
        Some (first,second,third) /\
      NoDup outerNames /\ NoDup middleNames /\ NoDup deepNames.
Proof.
  intros outer middle deep outerNames middleNames deepNames
    [first [Hfirst Hnfirst]]
    [second [Hsecond Hnsecond]]
    [third [Hthird Hnthird]].
  exists first,second,third.
  unfold replayThreeStages.
  rewrite Hfirst,Hsecond,Hthird.
  repeat split; assumption || reflexivity.
Qed.

Theorem data05d_missing_outer_has_no_successor :
  forall a b c an bn cn,
    D.productRestorationPlan a an = None ->
    replayThreeStages a b c an bn cn = None.
Proof.
  intros a b c an bn cn H.
  unfold replayThreeStages.
  now rewrite H.
Qed.

Theorem data05d_missing_middle_has_no_later_successor :
  forall a b c an bn cn,
    D.productRestorationPlan b bn = None ->
    replayThreeStages a b c an bn cn = None.
Proof.
  intros a b c an bn cn H.
  unfold replayThreeStages.
  destruct (D.productRestorationPlan a an);
    [now rewrite H|reflexivity].
Qed.

Theorem data05d_missing_deep_has_no_terminal_successor :
  forall a b c an bn cn,
    D.productRestorationPlan c cn = None ->
    replayThreeStages a b c an bn cn = None.
Proof.
  intros a b c an bn cn H.
  unfold replayThreeStages.
  destruct (D.productRestorationPlan a an); [|reflexivity].
  destruct (D.productRestorationPlan b bn); [now rewrite H|reflexivity].
Qed.

Theorem data05d_successful_three_stage_exact_arity :
  forall a b c an bn cn first second third,
    replayThreeStages a b c an bn cn = Some (first,second,third) ->
    List.length a = List.length an /\
    List.length b = List.length bn /\
    List.length c = List.length cn.
Proof.
  intros a b c an bn cn first second third H.
  unfold replayThreeStages in H.
  destruct (D.productRestorationPlan a an) as [p1|] eqn:H1;
    try discriminate.
  destruct (D.productRestorationPlan b bn) as [p2|] eqn:H2;
    try discriminate.
  destruct (D.productRestorationPlan c cn) as [p3|] eqn:H3;
    try discriminate.
  inversion H; subst; clear H.
  repeat split.
  - exact (proj1 (D.restoration_plan_success_has_exact_lengths
      a an first H1)).
  - exact (proj1 (D.restoration_plan_success_has_exact_lengths
      b bn second H2)).
  - exact (proj1 (D.restoration_plan_success_has_exact_lengths
      c cn third H3)).
Qed.

Theorem data05d_successful_terminal_preserves_exact_leaf :
  forall a b c an bn cn first second third index leaf owner,
    replayThreeStages a b c an bn cn = Some (first,second,third) ->
    nth_error c index = Some leaf ->
    nth_error cn index = Some owner ->
    nth_error third index = Some
      (D.mkRestoredProductBinding owner
        (D.productElementMode leaf) (D.productElementType leaf)).
Proof.
  intros a b c an bn cn first second third index leaf owner
    H Hleaf Howner.
  unfold replayThreeStages in H.
  destruct (D.productRestorationPlan a an) as [p1|] eqn:H1;
    try discriminate.
  destruct (D.productRestorationPlan b bn) as [p2|] eqn:H2;
    try discriminate.
  destruct (D.productRestorationPlan c cn) as [p3|] eqn:H3;
    try discriminate.
  inversion H; subst; clear H.
  eapply D.restoration_plan_preserves_exact_element_contract; eauto.
Qed.

Print Assumptions data05d_checked_three_stage_plan_replays.
Print Assumptions data05d_missing_outer_has_no_successor.
Print Assumptions data05d_missing_middle_has_no_later_successor.
Print Assumptions data05d_missing_deep_has_no_terminal_successor.
Print Assumptions data05d_successful_three_stage_exact_arity.
Print Assumptions data05d_successful_terminal_preserves_exact_leaf.
