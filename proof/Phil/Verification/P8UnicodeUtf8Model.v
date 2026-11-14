From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

(*
  P8-C1: byte-accurate grammar for one Unicode scalar encoded in UTF-8.
  The values below are octets represented by nat, not Haskell Text and not
  a native checker credential. No axioms, Admitted or untracked premises.
  Native Text.Encoding <-> this grammar is tested independently, not proved
  by a Haskell operational semantics. The numeric-scalar-to-octets converse
  and full stream parser remain explicit separate obligations.
*)

Inductive P8Utf8ScalarOctets : Type :=
| P8Utf8One : nat -> P8Utf8ScalarOctets
| P8Utf8Two : nat -> nat -> P8Utf8ScalarOctets
| P8Utf8Three : nat -> nat -> nat -> P8Utf8ScalarOctets
| P8Utf8Four : nat -> nat -> nat -> nat -> P8Utf8ScalarOctets.

Definition p8_octet_between (low high value : nat) : bool :=
  (low <=? value) && (value <=? high).

(* The E0 / ED and F0 / F4 restrictions exclude overlong encodings,
   surrogates and values above U+10FFFF at the *byte grammar* boundary. *)
Definition p8_utf8_scalar_wellformed (s : P8Utf8ScalarOctets) : bool :=
  match s with
  | P8Utf8One a =>
      p8_octet_between 0 127 a
  | P8Utf8Two a b =>
      p8_octet_between 194 223 a &&
      p8_octet_between 128 191 b
  | P8Utf8Three a b c =>
      p8_octet_between 224 239 a &&
      p8_octet_between 128 191 b &&
      p8_octet_between 128 191 c &&
      (if a =? 224 then p8_octet_between 160 191 b
       else if a =? 237 then p8_octet_between 128 159 b
       else true)
  | P8Utf8Four a b c d =>
      p8_octet_between 240 244 a &&
      p8_octet_between 128 191 b &&
      p8_octet_between 128 191 c &&
      p8_octet_between 128 191 d &&
      (if a =? 240 then p8_octet_between 144 191 b
       else if a =? 244 then p8_octet_between 128 143 b
       else true)
  end.

Definition p8_utf8_scalar_bytes (s : P8Utf8ScalarOctets) : list nat :=
  match s with
  | P8Utf8One a => [a]
  | P8Utf8Two a b => [a; b]
  | P8Utf8Three a b c => [a; b; c]
  | P8Utf8Four a b c d => [a; b; c; d]
  end.

(* Exact single-code-point parser: no incomplete or trailing octets.
   This is deliberately not advertised as a full Text stream parser. *)
Definition p8_decode_exact_scalar (bytes : list nat) : option P8Utf8ScalarOctets :=
  match bytes with
  | [a] =>
      let s := P8Utf8One a in
      if p8_utf8_scalar_wellformed s then Some s else None
  | [a; b] =>
      let s := P8Utf8Two a b in
      if p8_utf8_scalar_wellformed s then Some s else None
  | [a; b; c] =>
      let s := P8Utf8Three a b c in
      if p8_utf8_scalar_wellformed s then Some s else None
  | [a; b; c; d] =>
      let s := P8Utf8Four a b c d in
      if p8_utf8_scalar_wellformed s then Some s else None
  | _ => None
  end.

(* Numeric interpretation of the canonical octets. For a wellformed input
   the grammar excludes overlong, surrogate and non-scalar UTF-8 shapes. *)
Definition p8_utf8_scalar_value (s : P8Utf8ScalarOctets) : nat :=
  match s with
  | P8Utf8One a => a
  | P8Utf8Two a b => (a - 192) * 64 + (b - 128)
  | P8Utf8Three a b c =>
      (a - 224) * 4096 + (b - 128) * 64 + (c - 128)
  | P8Utf8Four a b c d =>
      (a - 240) * 262144 + (b - 128) * 4096 +
      (c - 128) * 64 + (d - 128)
  end.

(* A machine-checkable domain contract, not an assumed Rocq proposition. *)
Definition p8_unicode_scalar (value : nat) : bool :=
  (value <=? 1114111) &&
  negb ((55296 <=? value) && (value <=? 57343)).

Theorem p8_exact_scalar_decode_encode :
  forall s, p8_utf8_scalar_wellformed s = true ->
    p8_decode_exact_scalar (p8_utf8_scalar_bytes s) = Some s.
Proof.
  intros s H.
  destruct s; simpl in *; rewrite H; reflexivity.
Qed.

Theorem p8_scalar_byte_encoding_injective :
  forall left right,
    p8_utf8_scalar_bytes left = p8_utf8_scalar_bytes right ->
    left = right.
Proof.
  intros left right H.
  destruct left; destruct right; simpl in H; congruence.
Qed.

Theorem p8_scalar_wellformed_has_exact_length :
  forall s,
    length (p8_utf8_scalar_bytes s) =
      match s with
      | P8Utf8One _ => 1
      | P8Utf8Two _ _ => 2
      | P8Utf8Three _ _ _ => 3
      | P8Utf8Four _ _ _ _ => 4
      end.
Proof. destruct s; reflexivity. Qed.

(* Single-code-point examples cover the 1/2/3/4-byte admitted grammar. *)
Example p8_nul_is_a_scalar :
  p8_decode_exact_scalar [0] = Some (P8Utf8One 0).
Proof. reflexivity. Qed.

Example p8_accent_e9_is_a_scalar :
  p8_decode_exact_scalar [195; 169] = Some (P8Utf8Two 195 169).
Proof. reflexivity. Qed.

Example p8_smile_1f642_is_a_scalar :
  p8_decode_exact_scalar [240; 159; 153; 130] =
    Some (P8Utf8Four 240 159 153 130).
Proof. reflexivity. Qed.

Example p8_reject_overlong_two_byte :
  p8_decode_exact_scalar [192; 128] = None.
Proof. reflexivity. Qed.

Example p8_reject_overlong_three_byte :
  p8_decode_exact_scalar [224; 128; 128] = None.
Proof. reflexivity. Qed.

Example p8_reject_surrogate :
  p8_decode_exact_scalar [237; 160; 128] = None.
Proof. reflexivity. Qed.

Example p8_reject_beyond_unicode :
  p8_decode_exact_scalar [244; 144; 128; 128] = None.
Proof. reflexivity. Qed.

Example p8_reject_bad_continuation :
  p8_decode_exact_scalar [226; 40; 161] = None.
Proof. reflexivity. Qed.

Example p8_reject_truncated :
  p8_decode_exact_scalar [240; 159; 153] = None.
Proof. reflexivity. Qed.

Example p8_reject_trailing_scalar_data :
  p8_decode_exact_scalar [0; 0] = None.
Proof. reflexivity. Qed.

Example p8_distinct_canonical_composed_decomposed :
  [195; 169] <> [101; 204; 129].
Proof. discriminate. Qed.

Print Assumptions p8_exact_scalar_decode_encode.
Print Assumptions p8_scalar_byte_encoding_injective.
Print Assumptions p8_scalar_wellformed_has_exact_length.
Print Assumptions p8_reject_surrogate.
Print Assumptions p8_reject_beyond_unicode.
