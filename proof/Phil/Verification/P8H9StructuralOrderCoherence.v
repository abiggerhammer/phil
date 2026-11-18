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

Print Assumptions p8_h9_compare_bytes_common_prefix.
Print Assumptions p8_h9_compare_bytes_proper_prefix.
Print Assumptions p8_h9_pairwise_implies_adjacent_members.
Print Assumptions p8_h9_pairwise_implies_adjacent_keys.
