From Coq Require Import List Bool Arith.PeanoNat Lia.
From Phil.Verification Require Import
  P8UnicodeUtf8Model P8D1UnicodeStreamModel P8D2StructuralOrderModel.
Import ListNotations.

(*
  P8-H8, proof-only preflight. These are pure C1/D1 byte-model
  propositions, NOT premises about any GHC, Text or Haskell executable.
*)

Lemma p8_h8_scalar_of_numeric_bounds :
  forall n,
    n <= 1114111 ->
    (n < 55296 \/ 57343 < n) ->
    p8_unicode_scalar n = true.
Proof.
  intros n Upper Outside.
  unfold p8_unicode_scalar.
  apply andb_true_iff; split.
  - apply Nat.leb_le. lia.
  - apply negb_true_iff.
    destruct ((55296 <=? n) && (n <=? 57343)) eqn:Inside.
    + apply andb_true_iff in Inside as [Lo Hi].
      apply Nat.leb_le in Lo.
      apply Nat.leb_le in Hi.
      lia.
    + reflexivity.
Qed.

Ltac p8_h8_unpack_octets :=
  repeat match goal with
  | H : (_ && _) = true |- _ =>
      apply andb_true_iff in H; destruct H
  | H : (_ <=? _) = true |- _ =>
      apply Nat.leb_le in H
  | H : (_ =? _) = true |- _ =>
      apply Nat.eqb_eq in H
  | H : (_ =? _) = false |- _ =>
      apply Nat.eqb_neq in H
  end.

Theorem p8_h8_c1_valid_scalar_value :
  forall scalar,
    p8_utf8_scalar_wellformed scalar = true ->
    p8_unicode_scalar (p8_utf8_scalar_value scalar) = true.
Proof.
  intros scalar Valid.
  destruct scalar as [a | a b | a b c | a b c d].
  - apply p8_h8_scalar_of_numeric_bounds.
    + cbn [p8_utf8_scalar_value].
      cbn [p8_utf8_scalar_wellformed] in Valid.
      unfold p8_octet_between in Valid.
      p8_h8_unpack_octets.
      Show.
      lia.
    + cbn [p8_utf8_scalar_value].
      cbn [p8_utf8_scalar_wellformed] in Valid.
      unfold p8_octet_between in Valid.
      p8_h8_unpack_octets.
      left; lia.
  - apply p8_h8_scalar_of_numeric_bounds;
      cbn [p8_utf8_scalar_wellformed p8_utf8_scalar_value] in *;
      unfold p8_octet_between in Valid;
      p8_h8_unpack_octets; first [lia | left; lia | right; lia].
  - apply p8_h8_scalar_of_numeric_bounds;
      cbn [p8_utf8_scalar_wellformed p8_utf8_scalar_value] in *;
      unfold p8_octet_between in Valid;
      destruct (a =? 224) eqn:E224;
      destruct (a =? 237) eqn:E237;
      cbn in Valid;
      p8_h8_unpack_octets; first [lia | left; lia | right; lia].
  - apply p8_h8_scalar_of_numeric_bounds;
      cbn [p8_utf8_scalar_wellformed p8_utf8_scalar_value] in *;
      unfold p8_octet_between in Valid;
      destruct (a =? 240) eqn:E240;
      destruct (a =? 244) eqn:E244;
      cbn in Valid;
      p8_h8_unpack_octets; first [lia | left; lia | right; lia].
Qed.

(* Canonical numeric encoder candidate, not yet a proved inverse. *)
Definition p8_h8_encode_scalar (n : nat) : P8Utf8ScalarOctets :=
  if n <? 128 then P8Utf8One n
  else if n <? 2048 then
    P8Utf8Two (192 + n / 64) (128 + n mod 64)
  else if n <? 65536 then
    P8Utf8Three (224 + n / 4096)
      (128 + (n / 64) mod 64) (128 + n mod 64)
  else
    P8Utf8Four (240 + n / 262144)
      (128 + (n / 4096) mod 64)
      (128 + (n / 64) mod 64) (128 + n mod 64).

Definition p8_h8_encode_if_scalar (n : nat)
  : option P8Utf8ScalarOctets :=
  if p8_unicode_scalar n then Some (p8_h8_encode_scalar n) else None.

(* Discriminating canonical boundary witnesses are model computations only. *)
Example p8_h8_nul :
  p8_h8_encode_if_scalar 0 = Some (P8Utf8One 0).
Proof. reflexivity. Qed.
Example p8_h8_7f_80 :
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 127) = [127] /\
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 128) = [194;128].
Proof. split; reflexivity. Qed.
Example p8_h8_7ff_800 :
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 2047) = [223;191] /\
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 2048) = [224;160;128].
Proof. split; reflexivity. Qed.
Example p8_h8_d7ff_e000 :
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 55295) = [237;159;191] /\
  p8_h8_encode_if_scalar 55296 = None /\
  p8_h8_encode_if_scalar 57343 = None /\
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 57344) = [238;128;128].
Proof. repeat split; reflexivity. Qed.
Example p8_h8_ffff_10000 :
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 65535) = [239;191;191] /\
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 65536) = [240;144;128;128].
Proof. split; reflexivity. Qed.
Example p8_h8_maximum :
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 1114111) = [244;143;191;191] /\
  p8_h8_encode_if_scalar 1114112 = None.
Proof. split; reflexivity. Qed.
Example p8_h8_composed_is_not_decomposed :
  p8_utf8_scalar_bytes (p8_h8_encode_scalar 233) <>
  p8_d1_encode [p8_h8_encode_scalar 101; p8_h8_encode_scalar 769].
Proof. discriminate. Qed.
Example p8_h8_reject_overlong :
  p8_decode_exact_scalar [192;128] = None /\
  p8_decode_exact_scalar [224;128;128] = None.
Proof. split; reflexivity. Qed.
Example p8_h8_reject_surrogate_and_overflow :
  p8_decode_exact_scalar [237;160;128] = None /\
  p8_decode_exact_scalar [244;144;128;128] = None.
Proof. split; reflexivity. Qed.

Print Assumptions p8_h8_scalar_of_numeric_bounds.
Print Assumptions p8_h8_c1_valid_scalar_value.
