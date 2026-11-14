From Coq Require Import List Ascii Sorting.Sorted.
Import ListNotations.

(*
 P8 partial byte-sequence representation model, NOT a model of Unicode
 scalar values or a checked accepted source. "ascii" is one octet here.
 Haskell Text/UTF-8 correspondence, native Ord, and opaque producer origin
 are independent UNPROVED obligations, not new axioms.
*)
Inductive P8FormShape : Type :=
| P8AtomBytes : list ascii -> P8FormShape
| P8OrderedChildren : list P8FormShape -> P8FormShape
| P8UnorderedCanonical : list P8FormShape -> P8FormShape
| P8RecordCanonical : list (list ascii * P8FormShape) -> P8FormShape.

Inductive P8FieldRole : Type :=
| P8Declaration | P8Interface | P8StaticKey | P8StaticValue.

Theorem p8_distinct_form_constructors :
  forall bytes ordered unordered record,
    P8AtomBytes bytes <> P8OrderedChildren ordered /\
    P8AtomBytes bytes <> P8UnorderedCanonical unordered /\
    P8AtomBytes bytes <> P8RecordCanonical record /\
    P8OrderedChildren ordered <> P8UnorderedCanonical unordered /\
    P8OrderedChildren ordered <> P8RecordCanonical record /\
    P8UnorderedCanonical unordered <> P8RecordCanonical record.
Proof.
  intros. repeat split; discriminate.
Qed.

Theorem p8_distinct_generic_field_roles :
  P8Declaration <> P8Interface /\
  P8StaticKey <> P8StaticValue /\
  P8Declaration <> P8StaticKey /\
  P8Interface <> P8StaticValue.
Proof.
  repeat split; discriminate.
Qed.

(*
 A canonical ascending finite key list has no repeats if strict order
 is irreflexive. This lemma does NOT establish that Haskell Ord equals
 the Rocq "lt" hypothesis, nor that a real native decoder constructs
 these proof objects. Native positives/negatives execute separately.
*)
Section CanonicalFiniteKeys.
  Context {Key : Type}.
  Variable lt : Key -> Key -> Prop.
  Hypothesis lt_irrefl : forall key, ~ lt key key.

  Lemma p8_forall_relation_member :
    forall key keys selected,
      Forall (lt key) keys ->
      In selected keys ->
      lt key selected.
  Proof.
    intros key keys selected Hall Hin.
    induction Hall as [|head tail Hhead Htail IH].
    - contradiction.
    - destruct Hin as [Heq | HtailIn].
      + subst. exact Hhead.
      + exact (IH HtailIn).
  Qed.

  Theorem p8_strictly_sorted_keys_have_no_duplicates :
    forall keys, StronglySorted lt keys -> NoDup keys.
  Proof.
    intros keys Hsorted.
    induction Hsorted as [|head tail Htail IH Hall].
    - constructor.
    - constructor.
      + intro Hin.
        apply (lt_irrefl head).
        exact (p8_forall_relation_member head tail head Hall Hin).
      + exact IH.
  Qed.
End CanonicalFiniteKeys.

Print Assumptions p8_distinct_form_constructors.
Print Assumptions p8_distinct_generic_field_roles.
Print Assumptions p8_strictly_sorted_keys_have_no_duplicates.
