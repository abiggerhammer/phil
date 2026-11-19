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
    rewrite Nat.compare_refl. simpl. apply IH.
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

(* Order reversal also descends through the ORIGINAL mutually
   inductive D2 comparisons; off-diagonal constructors use D2's fixed
   Atom < Ordered < Unordered < Record rank, not wire-tag ordering. *)
Fixpoint p8_h9_compare_form_reversal (f : P8D2Form) {struct f} :
  forall g, p8_d2_compare_form f g =
    p8_h9_reverse_compare (p8_d2_compare_form g f)
with p8_h9_compare_forms_reversal (fs : P8D2Forms) {struct fs} :
  forall gs, p8_d2_compare_forms fs gs =
    p8_h9_reverse_compare (p8_d2_compare_forms gs fs)
with p8_h9_compare_fields_reversal (fs : P8D2Fields) {struct fs} :
  forall gs, p8_d2_compare_fields fs gs =
    p8_h9_reverse_compare (p8_d2_compare_fields gs fs).
Proof.
  - destruct f as [bytes | fs | fs | fs]; intros g;
      destruct g as [other | gs | gs | gs]; simpl;
      try reflexivity.
    + apply p8_h9_compare_bytes_reversal.
    + apply p8_h9_compare_forms_reversal.
    + apply p8_h9_compare_forms_reversal.
    + apply p8_h9_compare_fields_reversal.
  - destruct fs as [| head tail]; intros gs;
      destruct gs as [| other rest]; simpl; try reflexivity.
    rewrite (p8_h9_compare_form_reversal head other).
    destruct (p8_d2_compare_form other head); simpl;
      try reflexivity.
    apply p8_h9_compare_forms_reversal.
  - destruct fs as [| key value tail]; intros gs;
      destruct gs as [| key' value' rest]; simpl; try reflexivity.
    rewrite (p8_h9_compare_bytes_reversal key key').
    destruct (p8_d2_compare_bytes key' key); simpl;
      try reflexivity.
    rewrite (p8_h9_compare_form_reversal value value').
    destruct (p8_d2_compare_form value' value); simpl;
      try reflexivity.
    apply p8_h9_compare_fields_reversal.
Defined.

(* The key-list half of the pairwise/adjacent equivalence can be
   completed independently of structural-form transitivity: original record
   ordering compares keys by the actual D2 strict byte comparator. *)
Lemma p8_h9_key_less_transitive :
  forall x y z,
    p8_d2_key_less x y = true ->
    p8_d2_key_less y z = true ->
    p8_d2_key_less x z = true.
Proof.
  intros x y z Hxy Hyz.
  unfold p8_d2_key_less in *.
  destruct (p8_d2_compare_bytes x y) eqn:XY; simpl in Hxy;
    try discriminate.
  destruct (p8_d2_compare_bytes y z) eqn:YZ; simpl in Hyz;
    try discriminate.
  rewrite (p8_h9_compare_bytes_lt_transitive x y z XY YZ).
  reflexivity.
Qed.

Lemma p8_h9_key_less_all_transitive :
  forall x y rest,
    p8_d2_key_less x y = true ->
    p8_d2_all_later_keys y rest = true ->
    p8_d2_all_later_keys x rest = true.
Proof.
  intros x y rest Hxy.
  induction rest as [| key value tail IH]; simpl.
  - intro _. reflexivity.
  - intro Hall.
    apply andb_true_iff in Hall as [Hyk Htail].
    apply andb_true_iff. split.
    + eapply p8_h9_key_less_transitive; eauto.
    + apply IH. exact Htail.
Qed.

Theorem p8_h9_adjacent_implies_pairwise_keys :
  forall fields,
    p8_h9_adjacent_keys fields = true ->
    p8_d2_strict_keys fields = true.
Proof.
  induction fields as [| key value tail IH]; simpl.
  - intro _. reflexivity.
  - destruct tail as [| next nextvalue more]; simpl.
    + intro _. reflexivity.
    + intro Adj.
      apply andb_true_iff in Adj as [KeyLess AdjTail].
      specialize (IH AdjTail).
      simpl in IH.
      apply andb_true_iff in IH as [NextAll MorePair].
      apply andb_true_iff. split.
      * apply andb_true_iff. split.
        -- exact KeyLess.
        -- eapply p8_h9_key_less_all_transitive; eauto.
      * apply andb_true_iff. split; assumption.
Qed.

Theorem p8_h9_adjacent_iff_pairwise_keys :
  forall fields,
    p8_h9_adjacent_keys fields = true <->
    p8_d2_strict_keys fields = true.
Proof.
  intro fields. split.
  - apply p8_h9_adjacent_implies_pairwise_keys.
  - apply p8_h9_pairwise_implies_adjacent_keys.
Qed.

(* The original D2 constructor rank never decreases along a
   strict structural comparison. Same-rank recursion is handled below. *)
Lemma p8_h9_compare_form_lt_rank_le :
  forall f g,
    p8_d2_compare_form f g = Lt ->
    p8_d2_rank f <= p8_d2_rank g.
Proof.
  intros f g H.
  destruct f; destruct g; simpl in *; try discriminate; lia.
Qed.

(* Mutually structural strict transitivity. The rank proof discharges every
   cross-constructor case, leaving only the four equal-constructor recursive
   cases. For field heads, the existing byte and nested-form comparators
   order key first, value next, before recursive field tails. *)
Fixpoint p8_h9_compare_form_lt_transitive (f : P8D2Form) {struct f} :
  forall g h,
    p8_d2_compare_form f g = Lt ->
    p8_d2_compare_form g h = Lt ->
    p8_d2_compare_form f h = Lt
with p8_h9_compare_forms_lt_transitive (fs : P8D2Forms) {struct fs} :
  forall gs hs,
    p8_d2_compare_forms fs gs = Lt ->
    p8_d2_compare_forms gs hs = Lt ->
    p8_d2_compare_forms fs hs = Lt
with p8_h9_compare_fields_lt_transitive (fs : P8D2Fields) {struct fs} :
  forall gs hs,
    p8_d2_compare_fields fs gs = Lt ->
    p8_d2_compare_fields gs hs = Lt ->
    p8_d2_compare_fields fs hs = Lt.
Proof.
  - intros g h Hfg Hgh.
    pose proof (p8_h9_compare_form_lt_rank_le f g Hfg) as Rfg.
    pose proof (p8_h9_compare_form_lt_rank_le g h Hgh) as Rgh.
    destruct (Nat.eq_dec (p8_d2_rank f) (p8_d2_rank h))
      as [EqualRanks | DifferentRanks].
    + assert (FGRanks : p8_d2_rank f = p8_d2_rank g) by lia.
      assert (GHRanks : p8_d2_rank g = p8_d2_rank h) by lia.
      destruct f; destruct g; destruct h; simpl in *; try lia.
      * eapply p8_h9_compare_bytes_lt_transitive; eassumption.
      * eapply p8_h9_compare_forms_lt_transitive; eassumption.
      * eapply p8_h9_compare_forms_lt_transitive; eassumption.
      * eapply p8_h9_compare_fields_lt_transitive; eassumption.
    + apply p8_d2_constructor_rank_lt. lia.
  - destruct fs as [| x xs]; intros gs hs Hfg Hgh;
      destruct gs as [| y ys]; destruct hs as [| z zs];
      simpl in *; try discriminate; try reflexivity.
    destruct (p8_d2_compare_form x y) eqn:Cxy;
      simpl in Hfg; try discriminate.
    + apply p8_h9_compare_form_eq_reflect in Cxy. subst y.
      destruct (p8_d2_compare_form x z) eqn:Cxz;
        simpl in Hgh; try discriminate.
      * apply p8_h9_compare_form_eq_reflect in Cxz. subst z.
        simpl. rewrite (p8_h9_compare_form_reflexive x).
        eapply p8_h9_compare_forms_lt_transitive; eassumption.
      * simpl. rewrite Cxz. reflexivity.
    + destruct (p8_d2_compare_form y z) eqn:Cyz;
        simpl in Hgh; try discriminate.
      * apply p8_h9_compare_form_eq_reflect in Cyz. subst z.
        simpl. rewrite Cxy. reflexivity.
      * assert (Cxz : p8_d2_compare_form x z = Lt).
        { eapply p8_h9_compare_form_lt_transitive; eassumption. }
        simpl. rewrite Cxz. reflexivity.
  - destruct fs as [| key value rest]; intros gs hs Hfg Hgh;
      destruct gs as [| key' value' mid];
      destruct hs as [| key'' value'' tail];
      simpl in *; try discriminate; try reflexivity.
    destruct (p8_d2_compare_bytes key key') eqn:Kxy;
      simpl in Hfg; try discriminate.
    + apply p8_h9_compare_bytes_eq_iff in Kxy. subst key'.
      destruct (p8_d2_compare_bytes key key'') eqn:Kxz.
      * apply p8_h9_compare_bytes_eq_iff in Kxz. subst key''.
        destruct (p8_d2_compare_form value value') eqn:Vxy;
          simpl in Hfg; try discriminate.
        -- apply p8_h9_compare_form_eq_reflect in Vxy.
           subst value'.
           destruct (p8_d2_compare_form value value'') eqn:Vxz;
             simpl in Hgh; try discriminate.
           ++ apply p8_h9_compare_form_eq_reflect in Vxz.
              subst value''.
              simpl.
              rewrite (p8_h9_compare_bytes_reflexive key).
              rewrite (p8_h9_compare_form_reflexive value).
              eapply p8_h9_compare_fields_lt_transitive; eassumption.
           ++ simpl.
              rewrite (p8_h9_compare_bytes_reflexive key).
              rewrite Vxz. reflexivity.
        -- destruct (p8_d2_compare_form value' value'') eqn:Vyz;
             simpl in Hgh; try discriminate.
           ++ apply p8_h9_compare_form_eq_reflect in Vyz.
              subst value''.
              simpl.
              rewrite (p8_h9_compare_bytes_reflexive key).
              rewrite Vxy. reflexivity.
           ++ assert (Vxz : p8_d2_compare_form value value'' = Lt).
              { eapply p8_h9_compare_form_lt_transitive; eassumption. }
              simpl.
              rewrite (p8_h9_compare_bytes_reflexive key).
              rewrite Vxz. reflexivity.
      * simpl. rewrite Kxz. reflexivity.
      * rewrite Kxz in Hgh. discriminate.
    + destruct (p8_d2_compare_bytes key' key'') eqn:Kyz;
        simpl in Hgh; try discriminate.
      * apply p8_h9_compare_bytes_eq_iff in Kyz. subst key''.
        simpl. rewrite Kxy. reflexivity.
      * assert (Kxz : p8_d2_compare_bytes key key'' = Lt).
        { eapply p8_h9_compare_bytes_lt_transitive; eassumption. }
        simpl. rewrite Kxz. reflexivity.
Defined.

(* The member-list converse now follows from TRUE strict transitivity
   of original recursively ordered D2 forms, without a foreign Ord axiom. *)
Lemma p8_h9_member_less_transitive :
  forall x y z,
    p8_d2_less x y = true ->
    p8_d2_less y z = true ->
    p8_d2_less x z = true.
Proof.
  intros x y z Hxy Hyz.
  unfold p8_d2_less in *.
  destruct (p8_d2_compare_form x y) eqn:XY; simpl in Hxy;
    try discriminate.
  destruct (p8_d2_compare_form y z) eqn:YZ; simpl in Hyz;
    try discriminate.
  rewrite (p8_h9_compare_form_lt_transitive x y z XY YZ).
  reflexivity.
Qed.

Lemma p8_h9_member_less_all_transitive :
  forall x y rest,
    p8_d2_less x y = true ->
    p8_d2_all_later_less y rest = true ->
    p8_d2_all_later_less x rest = true.
Proof.
  intros x y rest Hxy.
  induction rest as [| member tail IH]; simpl.
  - intro _. reflexivity.
  - intro Hall.
    apply andb_true_iff in Hall as [Hym Htail].
    apply andb_true_iff. split.
    + eapply p8_h9_member_less_transitive; eauto.
    + apply IH. exact Htail.
Qed.

Theorem p8_h9_adjacent_implies_pairwise_members :
  forall members,
    p8_h9_adjacent_members members = true ->
    p8_d2_strict_members members = true.
Proof.
  induction members as [| member tail IH]; simpl.
  - intro _. reflexivity.
  - destruct tail as [| next more]; simpl.
    + intro _. reflexivity.
    + intro Adj.
      apply andb_true_iff in Adj as [MemberLess AdjTail].
      specialize (IH AdjTail).
      simpl in IH.
      apply andb_true_iff in IH as [NextAll MorePair].
      apply andb_true_iff. split.
      * apply andb_true_iff. split.
        -- exact MemberLess.
        -- eapply p8_h9_member_less_all_transitive; eauto.
      * apply andb_true_iff. split; assumption.
Qed.

Theorem p8_h9_adjacent_iff_pairwise_members :
  forall members,
    p8_h9_adjacent_members members = true <->
    p8_d2_strict_members members = true.
Proof.
  intro members. split.
  - apply p8_h9_adjacent_implies_pairwise_members.
  - apply p8_h9_pairwise_implies_adjacent_members.
Qed.

Example p8_h9_unicode_nfc_nfd_distinct :
  p8_d2_compare_form
    (P8D2Atom [101; 204; 129])
    (P8D2Atom [195; 169]) = Lt.
Proof. reflexivity. Qed.

Example p8_h9_structural_rank_not_wire_tag :
  p8_d2_compare_form (P8D2Unordered P8D2Nil)
    (P8D2Record P8D2FieldNil) = Lt /\
  (117 <? 114) = false.
Proof. split; reflexivity. Qed.

Example p8_h9_member_prefix_order :
  p8_d2_compare_forms P8D2Nil
    (P8D2Cons (P8D2Atom [0]) P8D2Nil) = Lt.
Proof. reflexivity. Qed.

Example p8_h9_reversed_members_not_adjacent :
  p8_h9_adjacent_members
    (P8D2Cons (P8D2Atom [98])
      (P8D2Cons (P8D2Atom [97]) P8D2Nil)) = false.
Proof. reflexivity. Qed.

Example p8_h9_duplicate_keys_not_adjacent :
  p8_h9_adjacent_keys
    (P8D2FieldCons [97] (P8D2Atom [])
      (P8D2FieldCons [97] (P8D2Atom []) P8D2FieldNil)) = false.
Proof. reflexivity. Qed.

Print Assumptions p8_h9_member_less_transitive.
Print Assumptions p8_h9_member_less_all_transitive.
Print Assumptions p8_h9_adjacent_implies_pairwise_members.
Print Assumptions p8_h9_adjacent_iff_pairwise_members.

Print Assumptions p8_h9_compare_form_lt_rank_le.
Print Assumptions p8_h9_compare_form_lt_transitive.
Print Assumptions p8_h9_compare_forms_lt_transitive.
Print Assumptions p8_h9_compare_fields_lt_transitive.

Print Assumptions p8_h9_key_less_transitive.
Print Assumptions p8_h9_key_less_all_transitive.
Print Assumptions p8_h9_adjacent_implies_pairwise_keys.
Print Assumptions p8_h9_adjacent_iff_pairwise_keys.

Print Assumptions p8_h9_compare_form_reversal.
Print Assumptions p8_h9_compare_forms_reversal.
Print Assumptions p8_h9_compare_fields_reversal.

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
