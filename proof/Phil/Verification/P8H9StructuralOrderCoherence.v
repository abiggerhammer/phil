From Coq Require Import List Bool Arith.PeanoNat Lia.
From Phil.Verification Require Import P8D2StructuralOrderModel.
Import ListNotations.

(*
  P8-H9: first pure mathematical preflight of the ORIGINAL D2 comparison.
  This file deliberately does NOT claim the converse adjacent->pairwise
  without a proof of comparator transitivity, nor native Text/Ord/Set/Map
  execution, selected accepted-object transport, or Phase 1 certification.
  Original D2 model definitions remain unchanged.
*)

(* A shared, identical byte prefix does not change the D2 byte comparison. *)
Lemma p8_h9_compare_bytes_common_prefix :
  forall prefix left right,
    p8_d2_compare_bytes (prefix ++ left) (prefix ++ right) =
    p8_d2_compare_bytes left right.
Proof.
  induction prefix as [| head tail IH]; intros left right.
  - reflexivity.
  - simpl. rewrite Nat.compare_refl. apply IH.
Qed.

(* A proper extension of a byte prefix sorts strictly after its prefix. *)
Lemma p8_h9_compare_bytes_proper_prefix :
  forall prefix next suffix,
    p8_d2_compare_bytes prefix (prefix ++ next :: suffix) = Lt.
Proof.
  induction prefix as [| head tail IH]; intros next suffix.
  - reflexivity.
  - simpl. rewrite Nat.compare_refl. apply IH.
Qed.

(* Adjacent order is an intentionally NEW local predicate; D2's original
   pairwise normalized-member predicate is NOT weakened or replaced. *)
Fixpoint p8_h9_adjacent_members (xs : P8D2Forms) : bool :=
  match xs with
  | P8D2Nil => true
  | P8D2Cons x tail =>
      match tail with
      | P8D2Nil => true
      | P8D2Cons y _ =>
          p8_d2_less x y && p8_h9_adjacent_members tail
      end
  end.

Fixpoint p8_h9_adjacent_keys (xs : P8D2Fields) : bool :=
  match xs with
  | P8D2FieldNil => true
  | P8D2FieldCons x _ tail =>
      match tail with
      | P8D2FieldNil => true
      | P8D2FieldCons y _ _ =>
          p8_d2_key_less x y && p8_h9_adjacent_keys tail
      end
  end.

(* The easier, assumption-free half of the future iff: the ORIGINAL
   pairwise predicate necessarily implies each adjacent inequality. *)
Theorem p8_h9_pairwise_implies_adjacent_members :
  forall xs,
    p8_d2_strict_members xs = true ->
    p8_h9_adjacent_members xs = true.
Proof.
  induction xs as [| x tail IH]; simpl.
  - intros _. reflexivity.
  - destruct tail as [| y rest]; simpl.
    + intros _. reflexivity.
    + intro H.
      apply andb_true_iff in H as [Hfront Htail].
      apply andb_true_iff; split.
      * apply andb_true_iff in Hfront as [Hxy _].
        exact Hxy.
      * apply IH. exact Htail.
Qed.

Theorem p8_h9_pairwise_implies_adjacent_keys :
  forall xs,
    p8_d2_strict_keys xs = true ->
    p8_h9_adjacent_keys xs = true.
Proof.
  induction xs as [| x value tail IH]; simpl.
  - intros _. reflexivity.
  - destruct tail as [| y next more]; simpl.
    + intros _. reflexivity.
    + intro H.
      apply andb_true_iff in H as [Hfront Htail].
      apply andb_true_iff; split.
      * apply andb_true_iff in Hfront as [Hxy _].
        exact Hxy.
      * apply IH. exact Htail.
Qed.

Example p8_h9_adjacent_empty_members :
  p8_h9_adjacent_members P8D2Nil = true.
Proof. reflexivity. Qed.

Example p8_h9_adjacent_duplicate_member :
  p8_h9_adjacent_members
    (P8D2Cons (P8D2Atom [97])
      (P8D2Cons (P8D2Atom [97]) P8D2Nil)) = false.
Proof. reflexivity. Qed.

Example p8_h9_adjacent_reversed_keys :
  p8_h9_adjacent_keys
    (P8D2FieldCons [98] (P8D2Atom [0])
      (P8D2FieldCons [97] (P8D2Atom [0]) P8D2FieldNil)) = false.
Proof. reflexivity. Qed.

(* Primitive algebra of the ORIGINAL D2 byte comparator: exact equality
   reflection, reversal and strict transitivity over arbitrary finite lists. *)
Lemma p8_h9_compare_bytes_reflexive :
  forall xs, p8_d2_compare_bytes xs xs = Eq.
Proof.
  induction xs as [| a tail IH]; simpl.
  - reflexivity.
  - rewrite Nat.compare_refl. exact IH.
Qed.

Lemma p8_h9_compare_bytes_eq_iff :
  forall xs ys,
    p8_d2_compare_bytes xs ys = Eq <-> xs = ys.
Proof.
  intros xs ys. split.
  - revert ys.
    induction xs as [| a tail IH]; intros [| b rest] H;
      simpl in H; try discriminate; try reflexivity.
    destruct (Nat.compare a b) eqn:Cmp; try discriminate.
    apply Nat.compare_eq_iff in Cmp. subst b.
    f_equal. apply IH. exact H.
  - intro E. subst ys. apply p8_h9_compare_bytes_reflexive.
Qed.

Definition p8_h9_reverse_compare (c : comparison) : comparison :=
  match c with Eq => Eq | Lt => Gt | Gt => Lt end.

Lemma p8_h9_compare_bytes_reversal :
  forall xs ys,
    p8_d2_compare_bytes xs ys =
    p8_h9_reverse_compare (p8_d2_compare_bytes ys xs).
Proof.
  induction xs as [| a tail IH]; intros [| b rest]; simpl;
    try reflexivity.
  destruct (Nat.compare a b) eqn:Cmp.
  - apply Nat.compare_eq_iff in Cmp. subst b.
    rewrite Nat.compare_refl. simpl. exact IH.
  - assert (Reverse : Nat.compare b a = Gt).
    { apply Nat.compare_gt_iff.
      apply Nat.compare_lt_iff in Cmp. lia. }
    rewrite Reverse. reflexivity.
  - assert (Reverse : Nat.compare b a = Lt).
    { apply Nat.compare_lt_iff.
      apply Nat.compare_gt_iff in Cmp. lia. }
    rewrite Reverse. reflexivity.
Qed.

Lemma p8_h9_compare_bytes_lt_transitive :
  forall xs ys zs,
    p8_d2_compare_bytes xs ys = Lt ->
    p8_d2_compare_bytes ys zs = Lt ->
    p8_d2_compare_bytes xs zs = Lt.
Proof.
  induction xs as [| a tail IH]; intros [| b rest] [| c final]
    Hxy Hyz; simpl in *; try discriminate; try reflexivity.
  destruct (Nat.compare a b) eqn:CmpAB; simpl in Hxy;
    try discriminate.
  - apply Nat.compare_eq_iff in CmpAB. subst b.
    destruct (Nat.compare a c) eqn:CmpAC.
    + apply Nat.compare_eq_iff in CmpAC. subst c.
      rewrite Nat.compare_refl.
      eapply IH; eassumption.
    + reflexivity.
    + rewrite CmpAC in Hyz. discriminate.
  - apply Nat.compare_lt_iff in CmpAB.
    destruct (Nat.compare b c) eqn:CmpBC; simpl in Hyz;
      try discriminate.
    + apply Nat.compare_eq_iff in CmpBC. subst c.
      assert (CmpAC : Nat.compare a b = Lt).
      { apply Nat.compare_lt_iff. lia. }
      rewrite CmpAC. reflexivity.
    + apply Nat.compare_lt_iff in CmpBC.
      assert (CmpAC : Nat.compare a c = Lt).
      { apply Nat.compare_lt_iff. lia. }
      rewrite CmpAC. reflexivity.
  - discriminate.
Qed.

(* Genuine mutually structural induction on the same three recursive D2
   datatypes used by the comparator. No fuel or a different surrogate AST. *)
Fixpoint p8_h9_compare_form_reflexive (f : P8D2Form) {struct f} :
  p8_d2_compare_form f f = Eq
with p8_h9_compare_forms_reflexive (xs : P8D2Forms) {struct xs} :
  p8_d2_compare_forms xs xs = Eq
with p8_h9_compare_fields_reflexive (xs : P8D2Fields) {struct xs} :
  p8_d2_compare_fields xs xs = Eq.
Proof.
  - destruct f as [bytes | forms | forms | fields]; simpl.
    + apply p8_h9_compare_bytes_reflexive.
    + apply p8_h9_compare_forms_reflexive.
    + apply p8_h9_compare_forms_reflexive.
    + apply p8_h9_compare_fields_reflexive.
  - destruct xs as [| head tail]; simpl.
    + reflexivity.
    + rewrite (p8_h9_compare_form_reflexive head).
      apply p8_h9_compare_forms_reflexive.
  - destruct xs as [| key value tail]; simpl.
    + reflexivity.
    + rewrite (p8_h9_compare_bytes_reflexive key).
      rewrite (p8_h9_compare_form_reflexive value).
      apply p8_h9_compare_fields_reflexive.
Defined.

(* A comparator result of Eq reflects actual constructor equality, down
   every recursive form, ordered/unordered list and named field sequence. *)
Fixpoint p8_h9_compare_form_eq_reflect (f : P8D2Form) {struct f} :
  forall g, p8_d2_compare_form f g = Eq -> f = g
with p8_h9_compare_forms_eq_reflect (fs : P8D2Forms) {struct fs} :
  forall gs, p8_d2_compare_forms fs gs = Eq -> fs = gs
with p8_h9_compare_fields_eq_reflect (fs : P8D2Fields) {struct fs} :
  forall gs, p8_d2_compare_fields fs gs = Eq -> fs = gs.
Proof.
  - destruct f as [bytes | fs | fs | fs]; intros g H;
      destruct g as [other | gs | gs | gs]; simpl in H;
      try discriminate.
    + apply p8_h9_compare_bytes_eq_iff in H. subst. reflexivity.
    + apply p8_h9_compare_forms_eq_reflect in H. subst. reflexivity.
    + apply p8_h9_compare_forms_eq_reflect in H. subst. reflexivity.
    + apply p8_h9_compare_fields_eq_reflect in H. subst. reflexivity.
  - destruct fs as [| first rest]; intros gs H;
      destruct gs as [| second rest']; simpl in H;
      try discriminate.
    + reflexivity.
    + destruct (p8_d2_compare_form first second) eqn:First;
        try discriminate.
      apply p8_h9_compare_form_eq_reflect in First.
      apply p8_h9_compare_forms_eq_reflect in H.
      subst. reflexivity.
  - destruct fs as [| key value rest]; intros gs H;
      destruct gs as [| key' value' rest']; simpl in H;
      try discriminate.
    + reflexivity.
    + destruct (p8_d2_compare_bytes key key') eqn:Key;
        try discriminate.
      destruct (p8_d2_compare_form value value') eqn:Value;
        try discriminate.
      apply p8_h9_compare_bytes_eq_iff in Key.
      apply p8_h9_compare_form_eq_reflect in Value.
      apply p8_h9_compare_fields_eq_reflect in H.
      subst. reflexivity.
Defined.

Print Assumptions p8_h9_compare_form_eq_reflect.
Print Assumptions p8_h9_compare_forms_eq_reflect.
Print Assumptions p8_h9_compare_fields_eq_reflect.

Print Assumptions p8_h9_compare_form_reflexive.
Print Assumptions p8_h9_compare_forms_reflexive.
Print Assumptions p8_h9_compare_fields_reflexive.

Print Assumptions p8_h9_compare_bytes_reflexive.
Print Assumptions p8_h9_compare_bytes_eq_iff.
Print Assumptions p8_h9_compare_bytes_reversal.
Print Assumptions p8_h9_compare_bytes_lt_transitive.

Print Assumptions p8_h9_compare_bytes_common_prefix.
Print Assumptions p8_h9_compare_bytes_proper_prefix.
Print Assumptions p8_h9_pairwise_implies_adjacent_members.
Print Assumptions p8_h9_pairwise_implies_adjacent_keys.
