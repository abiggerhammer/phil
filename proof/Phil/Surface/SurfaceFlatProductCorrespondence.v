From Stdlib Require Import Lists.List Bool.Bool.
Import ListNotations.

From Phil.Core Require Import Syntax DataMode DataProduct.

(*
  FSEM-01: a finite flat-product contract checker over the already existing
  abstract Core Ty and exact ProductElementContract carriers.

  This models the elementwise return-match gate introduced in Haskell: a
  successful equality decision must preserve every ordered mode and Ty, and
  therefore the aggregate mode cannot weaken any element. The Haskell
  implementation and Rocq's abstract Ty are not definitionally linked.
  The premise eqTy_sound is explicit: no Haskell Eq/Ty or parser theorem is
  claimed here. This file has no new axioms or admitted obligations.
*)

Definition sameProductMode (left right : Mode) : bool :=
  match left, right with
  | Unrestricted, Unrestricted => true
  | Affine, Affine => true
  | Linear, Linear => true
  | _, _ => false
  end.

Lemma same_product_mode_refl :
  forall mode, sameProductMode mode mode = true.
Proof. intros []; reflexivity. Qed.

Lemma same_product_mode_true :
  forall first second,
    sameProductMode first second = true -> first = second.
Proof.
  intros first second; destruct first, second; simpl;
    try discriminate; reflexivity.
Qed.

Definition sameProductElement
  (eqTy : Ty -> Ty -> bool)
  (expected actual : ProductElementContract) : bool :=
  sameProductMode
    (productElementMode expected) (productElementMode actual) &&
  eqTy (productElementType expected) (productElementType actual).

Fixpoint matchFlatProduct
  (eqTy : Ty -> Ty -> bool)
  (expected actual : list ProductElementContract) : bool :=
  match expected, actual with
  | [], [] => true
  | first :: rest, actualFirst :: actualRest =>
      sameProductElement eqTy first actualFirst &&
      matchFlatProduct eqTy rest actualRest
  | _, _ => false
  end.

Theorem checked_flat_product_preserves_exact_ordered_contract :
  forall eqTy,
    (forall first second, eqTy first second = true -> first = second) ->
    forall expected actual,
      matchFlatProduct eqTy expected actual = true ->
      expected = actual.
Proof.
  intros eqTy Heq expected.
  induction expected as [| [expectedMode expectedTy] rest IH];
    intros actual Hmatch.
  - destruct actual as [| actualFirst actualRest]; simpl in Hmatch;
      try discriminate; reflexivity.
  - destruct actual as [| [actualMode actualTy] actualRest];
      simpl in Hmatch; try discriminate.
    apply andb_true_iff in Hmatch as [Hhead Hrest].
    unfold sameProductElement in Hhead; simpl in Hhead.
    apply andb_true_iff in Hhead as [Hmode Hty].
    apply same_product_mode_true in Hmode.
    apply Heq in Hty.
    subst.
    f_equal.
    now apply IH.
Qed.

Theorem checked_flat_product_preserves_arity :
  forall eqTy,
    (forall first second, eqTy first second = true -> first = second) ->
    forall expected actual,
      matchFlatProduct eqTy expected actual = true ->
      length expected = length actual.
Proof.
  intros eqTy Heq expected actual Hmatch.
  apply (checked_flat_product_preserves_exact_ordered_contract
    eqTy Heq) in Hmatch.
  now subst.
Qed.

Theorem checked_flat_product_preserves_each_index :
  forall eqTy,
    (forall first second, eqTy first second = true -> first = second) ->
    forall expected actual index element,
      matchFlatProduct eqTy expected actual = true ->
      nth_error expected index = Some element ->
      nth_error actual index = Some element.
Proof.
  intros eqTy Heq expected actual index element Hmatch Hnth.
  apply (checked_flat_product_preserves_exact_ordered_contract
    eqTy Heq) in Hmatch.
  now subst.
Qed.

Theorem checked_flat_product_aggregate_mode_bounds_every_element :
  forall eqTy,
    (forall first second, eqTy first second = true -> first = second) ->
    forall expected actual element,
      matchFlatProduct eqTy expected actual = true ->
      In element expected ->
      modeLe (productElementMode element) (deriveProductMode actual).
Proof.
  intros eqTy Heq expected actual element Hmatch Hin.
  apply (checked_flat_product_preserves_exact_ordered_contract
    eqTy Heq) in Hmatch.
  subst.
  now apply product_mode_bounds_every_element.
Qed.

Theorem checked_flat_product_rejects_wrong_arity :
  forall eqTy,
    (forall first second, eqTy first second = true -> first = second) ->
    forall expected actual,
      length expected <> length actual ->
      matchFlatProduct eqTy expected actual = false.
Proof.
  intros eqTy Heq expected actual Hlength.
  destruct (matchFlatProduct eqTy expected actual) eqn:Hmatch;
    try reflexivity.
  exfalso.
  apply Hlength.
  eapply checked_flat_product_preserves_arity.
  - exact Heq.
  - exact Hmatch.
Qed.

Theorem checked_flat_product_accepts_identical_contract :
  forall eqTy,
    (forall ty, eqTy ty ty = true) ->
    forall elements,
      matchFlatProduct eqTy elements elements = true.
Proof.
  intros eqTy Heq elements.
  induction elements as [|[mode ty] rest IH]; simpl.
  - reflexivity.
  - unfold sameProductElement; simpl.
    rewrite same_product_mode_refl, Heq, IH.
    reflexivity.
Qed.
