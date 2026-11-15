From Coq Require Import List Bool Arith.PeanoNat Lia.
From Phil.Verification Require Import P8D1UnicodeStreamModel.
Import ListNotations.

(*
 P8-D2: a mutually inductive, unbounded FINITE recursive structural
 representation.  A text payload is its strict D1 UTF-8 octet stream;
 it is not a nat encoding for Phil identities or a model of Data.Text.
 The comparison follows the *derived Haskell constructor order* rather
 than the lexical order of wire tags: Atom < Ordered < Unordered < Record.
 Every recursive comparison is structural, with no artificial fuel bound.
*)
Inductive P8D2Form : Type :=
| P8D2Atom : list nat -> P8D2Form
| P8D2Ordered : P8D2Forms -> P8D2Form
| P8D2Unordered : P8D2Forms -> P8D2Form
| P8D2Record : P8D2Fields -> P8D2Form
with P8D2Forms : Type :=
| P8D2Nil : P8D2Forms
| P8D2Cons : P8D2Form -> P8D2Forms -> P8D2Forms
with P8D2Fields : Type :=
| P8D2FieldNil : P8D2Fields
| P8D2FieldCons : list nat -> P8D2Form -> P8D2Fields -> P8D2Fields.

Fixpoint p8_d2_compare_bytes (xs ys : list nat) {struct xs} : comparison :=
  match xs, ys with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | a :: tail, b :: rest =>
      match Nat.compare a b with
      | Eq => p8_d2_compare_bytes tail rest
      | other => other
      end
  end.

(* Lexicographic recursion descends through three genuine mutually
   inductive structures.  The sibling list and named-field list are
   distinct; sorting their serialized bytes would be incorrect. *)
Fixpoint p8_d2_compare_form (a b : P8D2Form) {struct a} : comparison :=
  match a, b with
  | P8D2Atom x, P8D2Atom y => p8_d2_compare_bytes x y
  | P8D2Atom _, _ => Lt
  | P8D2Ordered _, P8D2Atom _ => Gt
  | P8D2Ordered xs, P8D2Ordered ys => p8_d2_compare_forms xs ys
  | P8D2Ordered _, _ => Lt
  | P8D2Unordered _, P8D2Atom _ => Gt
  | P8D2Unordered _, P8D2Ordered _ => Gt
  | P8D2Unordered xs, P8D2Unordered ys => p8_d2_compare_forms xs ys
  | P8D2Unordered _, P8D2Record _ => Lt
  | P8D2Record xs, P8D2Record ys => p8_d2_compare_fields xs ys
  | P8D2Record _, _ => Gt
  end
with p8_d2_compare_forms (xs ys : P8D2Forms) {struct xs} : comparison :=
  match xs, ys with
  | P8D2Nil, P8D2Nil => Eq
  | P8D2Nil, P8D2Cons _ _ => Lt
  | P8D2Cons _ _, P8D2Nil => Gt
  | P8D2Cons x rest, P8D2Cons y other =>
      match p8_d2_compare_form x y with
      | Eq => p8_d2_compare_forms rest other
      | compared => compared
      end
  end
with p8_d2_compare_fields (xs ys : P8D2Fields) {struct xs} : comparison :=
  match xs, ys with
  | P8D2FieldNil, P8D2FieldNil => Eq
  | P8D2FieldNil, P8D2FieldCons _ _ _ => Lt
  | P8D2FieldCons _ _ _, P8D2FieldNil => Gt
  | P8D2FieldCons key value rest, P8D2FieldCons key' value' other =>
      match p8_d2_compare_bytes key key' with
      | Eq =>
          match p8_d2_compare_form value value' with
          | Eq => p8_d2_compare_fields rest other
          | compared => compared
          end
      | compared => compared
      end
  end.

Definition p8_d2_rank (f : P8D2Form) : nat :=
  match f with
  | P8D2Atom _ => 0
  | P8D2Ordered _ => 1
  | P8D2Unordered _ => 2
  | P8D2Record _ => 3
  end.

Definition p8_d2_less (a b : P8D2Form) : bool :=
  match p8_d2_compare_form a b with Lt => true | _ => false end.
Definition p8_d2_key_less (a b : list nat) : bool :=
  match p8_d2_compare_bytes a b with Lt => true | _ => false end.

(* Pairwise, not just adjacent, strict membership/key ordering.  This
   prevents silently assuming transitivity of a foreign native comparator. *)
Fixpoint p8_d2_all_later_less (x : P8D2Form) (xs : P8D2Forms)
  {struct xs} : bool :=
  match xs with
  | P8D2Nil => true
  | P8D2Cons y rest =>
      p8_d2_less x y && p8_d2_all_later_less x rest
  end.
Fixpoint p8_d2_strict_members (xs : P8D2Forms) : bool :=
  match xs with
  | P8D2Nil => true
  | P8D2Cons x rest =>
      p8_d2_all_later_less x rest && p8_d2_strict_members rest
  end.
Fixpoint p8_d2_all_later_keys (x : list nat) (xs : P8D2Fields)
  {struct xs} : bool :=
  match xs with
  | P8D2FieldNil => true
  | P8D2FieldCons y _ rest =>
      p8_d2_key_less x y && p8_d2_all_later_keys x rest
  end.
Fixpoint p8_d2_strict_keys (xs : P8D2Fields) : bool :=
  match xs with
  | P8D2FieldNil => true
  | P8D2FieldCons key _ rest =>
      p8_d2_all_later_keys key rest && p8_d2_strict_keys rest
  end.

Definition p8_d2_text_valid (bytes : list nat) : bool :=
  match p8_d1_decode bytes with
  | Some _ => true
  | None => false
  end.

(* Normalized structural domain: all text bytes are strictly decoded by
   D1, every recursive child is valid, and unordered/record collections
   are strictly pairwise ordered, rather than silently deduplicated. *)
Fixpoint p8_d2_valid_form (f : P8D2Form) {struct f} : bool :=
  match f with
  | P8D2Atom txt => p8_d2_text_valid txt
  | P8D2Ordered xs => p8_d2_valid_forms xs
  | P8D2Unordered xs =>
      p8_d2_strict_members xs && p8_d2_valid_forms xs
  | P8D2Record xs =>
      p8_d2_strict_keys xs && p8_d2_valid_fields xs
  end
with p8_d2_valid_forms (xs : P8D2Forms) {struct xs} : bool :=
  match xs with
  | P8D2Nil => true
  | P8D2Cons x rest =>
      p8_d2_valid_form x && p8_d2_valid_forms rest
  end
with p8_d2_valid_fields (xs : P8D2Fields) {struct xs} : bool :=
  match xs with
  | P8D2FieldNil => true
  | P8D2FieldCons key value rest =>
      p8_d2_text_valid key &&
      p8_d2_valid_form value &&
      p8_d2_valid_fields rest
  end.

(* D/V/Q/M are distinct typed roles; they may carry the same UTF-8
   bytes but cannot be interchanged by constructor equality. *)
Inductive P8D2Role : Type :=
| P8D2Declaration | P8D2Interface | P8D2ParameterKey
| P8D2ParameterValue.
Record P8D2Application : Type := {
  p8_d2_declaration : list nat;
  p8_d2_interface : list nat;
  p8_d2_arguments : P8D2Fields
}.
Definition p8_d2_valid_application (app : P8D2Application) : bool :=
  p8_d2_text_valid (p8_d2_declaration app) &&
  p8_d2_text_valid (p8_d2_interface app) &&
  p8_d2_strict_keys (p8_d2_arguments app) &&
  p8_d2_valid_fields (p8_d2_arguments app).

Theorem p8_d2_constructor_rank_lt :
  forall x y, p8_d2_rank x < p8_d2_rank y ->
              p8_d2_compare_form x y = Lt.
Proof.
  intros x y H; destruct x; destruct y; simpl in *;
    try lia; reflexivity.
Qed.
Theorem p8_d2_constructor_rank_gt :
  forall x y, p8_d2_rank y < p8_d2_rank x ->
              p8_d2_compare_form x y = Gt.
Proof.
  intros x y H; destruct x; destruct y; simpl in *;
    try lia; reflexivity.
Qed.

Lemma p8_d2_byte_compare_refl :
  forall bytes, p8_d2_compare_bytes bytes bytes = Eq.
Proof.
  induction bytes as [|a tail IH]; simpl.
  - reflexivity.
  - rewrite Nat.compare_refl. exact IH.
Qed.

Lemma p8_d2_key_less_irrefl :
  forall key, p8_d2_key_less key key = false.
Proof.
  intro key. unfold p8_d2_key_less.
  rewrite p8_d2_byte_compare_refl. reflexivity.
Qed.

Theorem p8_d2_adjacent_duplicate_key_rejected :
  forall key x y tail,
    p8_d2_strict_keys
      (P8D2FieldCons key x (P8D2FieldCons key y tail)) = false.
Proof.
  intros key x y tail.
  cbn [p8_d2_strict_keys p8_d2_all_later_keys].
  rewrite p8_d2_key_less_irrefl. reflexivity.
Qed.

Theorem p8_d2_duplicate_record_invalid :
  forall key x y tail,
    p8_d2_valid_form
      (P8D2Record
        (P8D2FieldCons key x (P8D2FieldCons key y tail))) = false.
Proof.
  intros key x y tail.
  cbn [p8_d2_valid_form].
  rewrite p8_d2_adjacent_duplicate_key_rejected.
  reflexivity.
Qed.

Theorem p8_d2_field_first_key_decides :
  forall key1 key2 v1 v2 tail1 tail2,
    p8_d2_compare_bytes key1 key2 = Lt ->
    p8_d2_compare_fields
      (P8D2FieldCons key1 v1 tail1)
      (P8D2FieldCons key2 v2 tail2) = Lt.
Proof.
  intros key1 key2 v1 v2 tail1 tail2 H.
  cbn [p8_d2_compare_fields]. rewrite H. reflexivity.
Qed.

Theorem p8_d2_roles_stay_distinct :
  P8D2Declaration <> P8D2Interface /\
  P8D2Declaration <> P8D2ParameterKey /\
  P8D2Interface <> P8D2ParameterValue /\
  P8D2ParameterKey <> P8D2ParameterValue.
Proof. repeat split; discriminate. Qed.

Example p8_d2_wire_order_counterexample :
  p8_d2_compare_form (P8D2Unordered P8D2Nil)
    (P8D2Record P8D2FieldNil) = Lt /\
  (117 <? 114) = false.
Proof. split; reflexivity. Qed.

Example p8_d2_nested_strict_unicode_positive :
  p8_d2_valid_form
    (P8D2Ordered (P8D2Cons (P8D2Atom [195;169])
      (P8D2Cons (P8D2Record (P8D2FieldCons [97]
        (P8D2Unordered (P8D2Cons (P8D2Atom [0])
          P8D2Nil)) P8D2FieldNil)) P8D2Nil))) = true.
Proof. reflexivity. Qed.

Example p8_d2_invalid_nested_utf8_negative :
  p8_d2_valid_form
    (P8D2Ordered (P8D2Cons (P8D2Atom [237;160;128])
      P8D2Nil)) = false.
Proof. reflexivity. Qed.

Example p8_d2_duplicate_set_member_negative :
  p8_d2_strict_members
    (P8D2Cons (P8D2Atom [97])
      (P8D2Cons (P8D2Atom [97]) P8D2Nil)) = false.
Proof. reflexivity. Qed.

Print Assumptions p8_d2_constructor_rank_lt.
Print Assumptions p8_d2_constructor_rank_gt.
Print Assumptions p8_d2_byte_compare_refl.
Print Assumptions p8_d2_adjacent_duplicate_key_rejected.
Print Assumptions p8_d2_duplicate_record_invalid.
Print Assumptions p8_d2_field_first_key_decides.
Print Assumptions p8_d2_roles_stay_distinct.
