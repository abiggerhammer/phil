From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.

From Phil.Core Require Import Syntax Context DataMode DataProduct.

(*
  FSEM-01 DATA-05A: conditional, finite two-stage nested product foundation.
  Native Haskell eliminates the original Linear product, then its Linear
  intermediate. The Haskell source driver independently checks both actual
  source-rooted lexical identities and exact Core Map/Set transitions.
  This Rocq model does NOT prove general source elaboration or Haskell
  implementation refinement; freshness, equality and successful transition
  premises are explicit.
*)

Module D := DataProduct.
Module C := Context.

Theorem data05a_two_stage_restoration_is_positional :
  forall outerLeft outerRight innerLeft innerRight
         outerFirst intermediate innerFirst innerSecond,
    D.productRestorationPlan [outerLeft;outerRight]
      [outerFirst;intermediate] =
      Some
        [D.mkRestoredProductBinding outerFirst
           (D.productElementMode outerLeft) (D.productElementType outerLeft);
         D.mkRestoredProductBinding intermediate
           (D.productElementMode outerRight) (D.productElementType outerRight)]
    /\
    D.productRestorationPlan [innerLeft;innerRight]
      [innerFirst;innerSecond] =
      Some
        [D.mkRestoredProductBinding innerFirst
           (D.productElementMode innerLeft) (D.productElementType innerLeft);
         D.mkRestoredProductBinding innerSecond
           (D.productElementMode innerRight) (D.productElementType innerRight)].
Proof. intros; split; reflexivity. Qed.

Theorem data05a_accepted_stages_preserve_exact_arity :
  forall outerElements outerNames innerElements innerNames,
    D.ProductEliminationAccepted outerElements outerNames ->
    D.ProductEliminationAccepted innerElements innerNames ->
    List.length outerNames = List.length outerElements /\
    List.length innerNames = List.length innerElements.
Proof.
  intros outerElements outerNames innerElements innerNames Houter Hinner.
  split.
  - now apply D.accepted_product_elimination_has_exact_arity.
  - now apply D.accepted_product_elimination_has_exact_arity.
Qed.

Theorem data05a_each_successful_stage_has_fresh_successors :
  forall outerElements outerNames innerElements innerNames,
    D.ProductEliminationAccepted outerElements outerNames ->
    D.ProductEliminationAccepted innerElements innerNames ->
    NoDup outerNames /\ NoDup innerNames.
Proof.
  intros outerElements outerNames innerElements innerNames Houter Hinner.
  split.
  - exact (D.accepted_product_elimination_has_unique_successors
      outerElements outerNames Houter).
  - exact (D.accepted_product_elimination_has_unique_successors
      innerElements innerNames Hinner).
Qed.

Theorem data05a_inner_leaf_contract_is_not_fabricated :
  forall innerElements innerNames index successor,
    D.ProductEliminationAccepted innerElements innerNames ->
    nth_error innerNames index = Some successor ->
    exists element plan,
      D.productRestorationPlan innerElements innerNames = Some plan /\
      nth_error innerElements index = Some element /\
      nth_error plan index =
        Some (D.mkRestoredProductBinding successor
          (D.productElementMode element) (D.productElementType element)).
Proof.
  intros.
  eapply D.accepted_product_elimination_fabricates_no_successor; eauto.
Qed.

Theorem data05a_inner_linear_member_keeps_nested_product_linear :
  forall first second,
    D.productElementMode first = Linear ->
    D.deriveProductMode [first;second] = Linear.
Proof.
  intros first second Hmode.
  eapply D.linear_element_makes_product_linear with (element := first).
  - left. reflexivity.
  - exact Hmode.
Qed.

Theorem data05a_two_linear_moves_do_not_resurrect_owners :
  forall packetName intermediateName initial afterOuter afterInner outerType innerType,
    C.consumeLinear packetName initial = C.Consumed outerType afterOuter ->
    C.consumeLinear intermediateName afterOuter = C.Consumed innerType afterInner ->
    String.eqb packetName intermediateName = false ->
    C.linearBindings afterInner packetName = None /\
    C.linearBindings afterInner intermediateName = None.
Proof.
  intros packetName intermediateName initial afterOuter afterInner
    outerType innerType Houter Hinner Hdistinct.
  split.
  - rewrite (C.consumeLinear_success_preserves_other_linear
      intermediateName packetName afterOuter afterInner innerType Hinner).
    + eapply D.consuming_linear_product_removes_owner; eauto.
    + exact Hdistinct.
  - eapply D.consuming_linear_product_removes_owner; eauto.
Qed.

Theorem data05a_no_third_consume_of_original :
  forall packetName intermediateName initial afterOuter afterInner outerType innerType
         laterType laterState,
    C.consumeLinear packetName initial = C.Consumed outerType afterOuter ->
    C.consumeLinear intermediateName afterOuter = C.Consumed innerType afterInner ->
    String.eqb packetName intermediateName = false ->
    C.consumeLinear packetName afterInner <> C.Consumed laterType laterState.
Proof.
  intros packetName intermediateName initial afterOuter afterInner
    outerType innerType laterType laterState Houter Hinner Hdistinct.
  pose proof (data05a_two_linear_moves_do_not_resurrect_owners
    packetName intermediateName initial afterOuter afterInner
    outerType innerType Houter Hinner Hdistinct) as [Habsent _].
  unfold C.consumeLinear.
  destruct (C.sharedLoans afterInner packetName); try discriminate.
  now rewrite Habsent.
Qed.

Print Assumptions data05a_two_stage_restoration_is_positional.
Print Assumptions data05a_accepted_stages_preserve_exact_arity.
Print Assumptions data05a_each_successful_stage_has_fresh_successors.
Print Assumptions data05a_inner_leaf_contract_is_not_fabricated.
Print Assumptions data05a_inner_linear_member_keeps_nested_product_linear.
Print Assumptions data05a_two_linear_moves_do_not_resurrect_owners.
Print Assumptions data05a_no_third_consume_of_original.
