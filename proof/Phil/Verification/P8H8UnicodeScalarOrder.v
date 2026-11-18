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
  | H : (_ <? _) = true |- _ =>
      apply Nat.ltb_lt in H
  | H : (_ <? _) = false |- _ =>
      apply Nat.ltb_ge in H
  end.

Theorem p8_h8_c1_valid_scalar_value :
  forall scalar,
    p8_utf8_scalar_wellformed scalar = true ->
    p8_unicode_scalar (p8_utf8_scalar_value scalar) = true.
Proof.
  intros scalar Valid.
  assert (BasicLimits :
    127 <= 1114111 /\ 127 < 55296 /\
    2047 <= 1114111 /\ 2047 < 55296 /\
    65535 <= 1114111 /\ 57343 < 65536).
  { repeat split;
      first [apply Nat.leb_le | apply Nat.ltb_lt];
      vm_compute; reflexivity. }
  destruct BasicLimits as
    [MaxOne [SurOne [MaxTwo [SurTwo [MaxThree SurFour]]]]].
  destruct scalar as [a | a b | a b c | a b c d].
  - apply p8_h8_scalar_of_numeric_bounds.
    + cbn [p8_utf8_scalar_value].
      cbn [p8_utf8_scalar_wellformed] in Valid.
      unfold p8_octet_between in Valid.
      p8_h8_unpack_octets.
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
  - assert (ThreeThresholds :
        15 * 4096 + 63 * 64 + 63 <= 65535 /\
        12 * 4096 + 63 * 64 + 63 < 55296 /\
        13 * 4096 + 31 * 64 + 63 < 55296 /\
        57343 < 14 * 4096).
    { repeat split; first [apply Nat.leb_le | apply Nat.ltb_lt];
        vm_compute; reflexivity. }
    destruct ThreeThresholds as [ThreeMax [ThreeLow [ThreeMiddle ThreeHigh]]].
    apply p8_h8_scalar_of_numeric_bounds;
      cbn [p8_utf8_scalar_wellformed p8_utf8_scalar_value] in *;
      unfold p8_octet_between in Valid;
      destruct (a =? 224) eqn:E224;
      destruct (a =? 237) eqn:E237;
      destruct (a <? 237) eqn:Below237;
      cbv iota in Valid;
      p8_h8_unpack_octets;
      first [nia | left; nia | right; nia].
  - assert (FourThresholds :
        3 * 262144 + 63 * 4096 + 63 * 64 + 63 <= 1114111 /\
        4 * 262144 + 15 * 4096 + 63 * 64 + 63 <= 1114111 /\
        57343 < 16 * 4096 /\
        57343 < 262144).
    { repeat split; first [apply Nat.leb_le | apply Nat.ltb_lt];
        vm_compute; reflexivity. }
    destruct FourThresholds as [FourLowMax [FourHighMax [FourLowMin FourHighMin]]].
    apply p8_h8_scalar_of_numeric_bounds;
      cbn [p8_utf8_scalar_wellformed p8_utf8_scalar_value] in *;
      unfold p8_octet_between in Valid;
      destruct (a =? 240) eqn:E240;
      destruct (a =? 244) eqn:E244;
      destruct (a <? 244) eqn:Below244;
      cbv iota in Valid;
      p8_h8_unpack_octets;
      first [lia | nia | left; nia | right; nia].
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

(* Division facts are exact for *all* naturals; unlike checked
   examples they do not rely on finite Unicode enumeration. *)
Lemma p8_h8_numeric_division_facts :
  forall n,
    n = 64 * (n / 64) + n mod 64 /\
    n = 4096 * (n / 4096) +
      64 * ((n / 64) mod 64) + n mod 64 /\
    n = 262144 * (n / 262144) +
      4096 * ((n / 4096) mod 64) +
      64 * ((n / 64) mod 64) + n mod 64.
Proof.
  intro n.
  pose proof (Nat.div_mod n 64 ltac:(lia)) as E64.
  pose proof (Nat.div_mod (n / 64) 64 ltac:(lia)) as E64_64.
  pose proof (Nat.div_mod n 4096 ltac:(lia)) as E4096.
  pose proof (Nat.div_mod (n / 4096) 64 ltac:(lia)) as E4096_64.
  pose proof (Nat.div_mod n 262144 ltac:(lia)) as E262144.
  pose proof (Nat.mod_upper_bound n 64 ltac:(lia)) as B64.
  pose proof (Nat.mod_upper_bound (n / 64) 64 ltac:(lia)) as B64_64.
  pose proof (Nat.mod_upper_bound n 4096 ltac:(lia)) as B4096.
  pose proof (Nat.mod_upper_bound (n / 4096) 64 ltac:(lia)) as B4096_64.
  pose proof (Nat.mod_upper_bound n 262144 ltac:(lia)) as B262144.
  assert (Q4096 : (n / 64) / 64 = n / 4096) by lia.
  assert (Q262144 : (n / 4096) / 64 = n / 262144) by lia.
  repeat split; lia.
Qed.

(* A numeric round trip, including out-of-range n. Shape validity is a
   *separate* theorem and is only asserted for admitted Unicode scalars. *)
Theorem p8_h8_numeric_encoder_value :
  forall n, p8_utf8_scalar_value (p8_h8_encode_scalar n) = n.
Proof.
  intros n.
  pose proof (p8_h8_numeric_division_facts n) as
    [D64 [D4096 D262144]].
  unfold p8_h8_encode_scalar.
  destruct (n <? 128) eqn:One.
  - reflexivity.
  - destruct (n <? 2048) eqn:Two.
    + cbn [p8_utf8_scalar_value]. lia.
    + destruct (n <? 65536) eqn:Three.
      * cbn [p8_utf8_scalar_value]. lia.
      * cbn [p8_utf8_scalar_value]. lia.
Qed.

(* The accepted numeric domain is an explicit bound and exclusion,
   not a property assumed of the native Haskell Char or Text types. *)
Lemma p8_h8_unicode_scalar_bounds :
  forall n, p8_unicode_scalar n = true ->
    n <= 1114111 /\ (n < 55296 \/ 57343 < n).
Proof.
  intros n Valid.
  unfold p8_unicode_scalar in Valid.
  apply andb_true_iff in Valid as [Upper Outside].
  apply Nat.leb_le in Upper.
  apply negb_true_iff in Outside.
  apply andb_false_iff in Outside as [Before | After].
  - apply Nat.leb_gt in Before. split; [lia | left; lia].
  - apply Nat.leb_gt in After. split; [lia | right; lia].
Qed.

(* This theorem is intentionally restricted to the admitted Unicode
   scalar numbers. The raw constructor has no wellformedness guarantee
   for numbers beyond U+10FFFF or within the surrogate interval. *)
Theorem p8_h8_numeric_encoder_wellformed :
  forall n, p8_unicode_scalar n = true ->
    p8_utf8_scalar_wellformed (p8_h8_encode_scalar n) = true.
Proof.
  intros n Valid.
  pose proof (p8_h8_unicode_scalar_bounds n Valid) as [Upper Outside].
  pose proof (p8_h8_numeric_division_facts n) as
    [D64 [D4096 D262144]].
  pose proof (Nat.mod_upper_bound n 64 ltac:(lia)) as M64.
  pose proof (Nat.mod_upper_bound (n / 64) 64 ltac:(lia)) as M64_64.
  pose proof (Nat.mod_upper_bound (n / 4096) 64 ltac:(lia)) as M4096_64.
  unfold p8_h8_encode_scalar.
  destruct (n <? 128) eqn:One.
  - apply Nat.ltb_lt in One.
    cbn [p8_utf8_scalar_wellformed].
    unfold p8_octet_between.
    repeat rewrite andb_true_iff.
    repeat split; apply Nat.leb_le; lia.
  - apply Nat.ltb_ge in One.
    destruct (n <? 2048) eqn:Two.
    + apply Nat.ltb_lt in Two.
      cbn [p8_utf8_scalar_wellformed].
      unfold p8_octet_between.
      repeat rewrite andb_true_iff.
      repeat split; apply Nat.leb_le; lia.
    + apply Nat.ltb_ge in Two.
      destruct (n <? 65536) eqn:Three.
      * apply Nat.ltb_lt in Three.
        cbn [p8_utf8_scalar_wellformed].
        unfold p8_octet_between.
        repeat rewrite andb_true_iff.
        repeat split; try (apply Nat.leb_le; lia).
        destruct (224 + n / 4096 =? 224) eqn:LeadE0.
        -- apply Nat.eqb_eq in LeadE0.
           repeat rewrite andb_true_iff.
           repeat split; apply Nat.leb_le; lia.
        -- destruct (224 + n / 4096 =? 237) eqn:LeadED.
           ++ apply Nat.eqb_eq in LeadED.
              destruct Outside as [Low | High].
              ** repeat rewrite andb_true_iff.
                 repeat split; apply Nat.leb_le; lia.
              ** repeat rewrite andb_true_iff.
                 repeat split; apply Nat.leb_le; lia.
           ++ reflexivity.
      * apply Nat.ltb_ge in Three.
        cbn [p8_utf8_scalar_wellformed].
        unfold p8_octet_between.
        repeat rewrite andb_true_iff.
        repeat split; try (apply Nat.leb_le; lia).
        destruct (240 + n / 262144 =? 240) eqn:LeadF0.
        -- apply Nat.eqb_eq in LeadF0.
           repeat rewrite andb_true_iff.
           repeat split; apply Nat.leb_le; lia.
        -- destruct (240 + n / 262144 =? 244) eqn:LeadF4.
           ++ apply Nat.eqb_eq in LeadF4.
              repeat rewrite andb_true_iff.
              repeat split; apply Nat.leb_le; lia.
           ++ reflexivity.
Qed.

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
Print Assumptions p8_h8_numeric_encoder_value.
Print Assumptions p8_h8_numeric_encoder_wellformed.
