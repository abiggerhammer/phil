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
    P8Utf8Four (240 + (n / 4096) / 64)
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
    n = (4096 * 64) * ((n / 4096) / 64) +
      4096 * ((n / 4096) mod 64) +
      64 * ((n / 64) mod 64) + n mod 64.
Proof.
  intro n.
  pose proof (Nat.div_mod n 64 ltac:(lia)) as E64.
  pose proof (Nat.div_mod (n / 64) 64 ltac:(lia)) as E64_64.
  pose proof (Nat.div_mod n 4096 ltac:(lia)) as E4096.
  pose proof (Nat.div_mod (n / 4096) 64 ltac:(lia)) as E4096_64.
  pose proof (Nat.mod_upper_bound n 64 ltac:(lia)) as B64.
  pose proof (Nat.mod_upper_bound (n / 64) 64 ltac:(lia)) as B64_64.
  pose proof (Nat.mod_upper_bound n 4096 ltac:(lia)) as B4096.
  pose proof (Nat.mod_upper_bound (n / 4096) 64 ltac:(lia)) as B4096_64.
  assert (Q4096 : (n / 64) / 64 = n / 4096) by lia.
  split; [lia |].
  split; [lia |].
  lia.
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
      * cbn [p8_utf8_scalar_value].
        assert (Radix : 262144 = 4096 * 64).
        { apply Nat.eqb_eq. vm_compute. reflexivity. }
        rewrite Radix.
        lia.
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
        assert (Bound65536 : 65536 = 4096 * 16).
        { apply Nat.eqb_eq. vm_compute. reflexivity. }
        rewrite Bound65536 in Three.
        assert (SurStart : 55296 = 4096 * 13 + 2048).
        { apply Nat.eqb_eq. vm_compute. reflexivity. }
        assert (SurEnd : 57343 = 4096 * 14 - 1).
        { apply Nat.eqb_eq. vm_compute. reflexivity. }
        rewrite SurStart, SurEnd in Outside.
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
        assert (Bound65536 : 65536 = 4096 * 16).
        { apply Nat.eqb_eq. vm_compute. reflexivity. }
        rewrite Bound65536 in Three.
        assert (MaxPlus : 1114111 + 1 = 4096 * 272).
        { apply Nat.eqb_eq. vm_compute. reflexivity. }
        assert (UpperStrict : n < 4096 * 272) by lia.
        cbn [p8_utf8_scalar_wellformed].
        unfold p8_octet_between.
        repeat rewrite andb_true_iff.
        repeat split; try (apply Nat.leb_le; lia).
        destruct (240 + (n / 4096) / 64 =? 240) eqn:LeadF0.
        -- apply Nat.eqb_eq in LeadF0.
           repeat rewrite andb_true_iff.
           repeat split; apply Nat.leb_le; lia.
        -- destruct (240 + (n / 4096) / 64 =? 244) eqn:LeadF4.
           ++ apply Nat.eqb_eq in LeadF4.
              repeat rewrite andb_true_iff.
              repeat split; apply Nat.leb_le; lia.
           ++ reflexivity.
Qed.


(* This is a total-on-admitted-numerals mathematical specification.
   It does not assert anything about a Haskell Text constructor. *)
Theorem p8_h8_numeric_encoder_admitted :
  forall n, p8_unicode_scalar n = true ->
    p8_h8_encode_if_scalar n = Some (p8_h8_encode_scalar n) /\
    p8_utf8_scalar_wellformed (p8_h8_encode_scalar n) = true /\
    p8_utf8_scalar_value (p8_h8_encode_scalar n) = n.
Proof.
  intros n Valid.
  split.
  - unfold p8_h8_encode_if_scalar. now rewrite Valid.
  - split.
    + now apply p8_h8_numeric_encoder_wellformed.
    + apply p8_h8_numeric_encoder_value.
Qed.

Theorem p8_h8_numeric_encoder_injective :
  forall n m,
    p8_h8_encode_scalar n = p8_h8_encode_scalar m -> n = m.
Proof.
  intros n m Equal.
  pose proof (f_equal p8_utf8_scalar_value Equal) as Values.
  rewrite !p8_h8_numeric_encoder_value in Values.
  exact Values.
Qed.

(* Each original C1 constructor has a disjoint numerical width interval.
   The E0/ED and F0/F4 guards are essential to the lower/upper bounds. *)
Lemma p8_h8_wellformed_width_bounds :
  forall s, p8_utf8_scalar_wellformed s = true ->
    match s with
    | P8Utf8One _ => p8_utf8_scalar_value s <= 127
    | P8Utf8Two _ _ =>
        128 <= p8_utf8_scalar_value s /\
        p8_utf8_scalar_value s <= 2047
    | P8Utf8Three _ _ _ =>
        2048 <= p8_utf8_scalar_value s /\
        p8_utf8_scalar_value s <= 65535
    | P8Utf8Four _ _ _ _ =>
        65536 <= p8_utf8_scalar_value s /\
        p8_utf8_scalar_value s <= 1114111
    end.
Proof.
  intros [a | a b | a b c | a b c d] Valid;
    cbn [p8_utf8_scalar_wellformed p8_utf8_scalar_value] in *;
    unfold p8_octet_between in Valid.
  - p8_h8_unpack_octets. lia.
  - p8_h8_unpack_octets. lia.
  - assert (MaxThree :
        65535 = 15 * 4096 + 63 * 64 + 63).
    { apply Nat.eqb_eq. vm_compute. reflexivity. }
    rewrite MaxThree.
    destruct (a =? 224) eqn:E224;
      destruct (a =? 237) eqn:E237;
      cbv iota in Valid;
      p8_h8_unpack_octets; split; lia.
  - assert (Radix : 262144 = 4096 * 64).
    { apply Nat.eqb_eq. vm_compute. reflexivity. }
    rewrite Radix.
    assert (MinFour : 65536 = 16 * 4096).
    { apply Nat.eqb_eq. vm_compute. reflexivity. }
    assert (MaxFour :
        1114111 = 4 * (4096 * 64) + 15 * 4096 +
                  63 * 64 + 63).
    { apply Nat.eqb_eq. vm_compute. reflexivity. }
    rewrite MinFour, MaxFour.
    destruct (a =? 240) eqn:E240;
      destruct (a =? 244) eqn:E244;
      cbv iota in Valid;
      p8_h8_unpack_octets; split; lia.
Qed.

(* Injectivity of the ORIGINAL C1 numeric interpretation on exactly its
   wellformed domain; this is distinct from encoder injectivity above.
   Finite width partitions and radix remainders force every octet equal. *)
Theorem p8_h8_c1_value_injective_on_valid :
  forall left right,
    p8_utf8_scalar_wellformed left = true ->
    p8_utf8_scalar_wellformed right = true ->
    p8_utf8_scalar_value left = p8_utf8_scalar_value right ->
    left = right.
Proof.
  intros left right ValidLeft ValidRight EqualValue.
  pose proof (p8_h8_wellformed_width_bounds left ValidLeft)
    as LeftBounds.
  pose proof (p8_h8_wellformed_width_bounds right ValidRight)
    as RightBounds.
  assert (Radix : 262144 = 4096 * 64).
  { apply Nat.eqb_eq. vm_compute. reflexivity. }
  assert (ThreeCap : 65535 = 15 * 4096 + 63 * 64 + 63).
  { apply Nat.eqb_eq. vm_compute. reflexivity. }
  assert (FourFloor : 65536 = 16 * 4096).
  { apply Nat.eqb_eq. vm_compute. reflexivity. }
  assert (FourCap :
      1114111 = 4 * (4096 * 64) + 15 * 4096 + 63 * 64 + 63).
  { apply Nat.eqb_eq. vm_compute. reflexivity. }
  destruct left; destruct right;
    cbn [p8_utf8_scalar_value] in *;
    try (rewrite Radix in *);
    try (rewrite ThreeCap in *);
    try (rewrite FourFloor in *);
    try (rewrite FourCap in *);
    try lia;
    cbn [p8_utf8_scalar_wellformed] in ValidLeft, ValidRight;
    unfold p8_octet_between in ValidLeft, ValidRight;
    repeat match goal with
    | H : context [if ?test then _ else _] |- _ =>
        destruct test eqn:?
    end;
    p8_h8_unpack_octets;
    f_equal; lia.
Qed.

Theorem p8_h8_encoder_c1_inverse :
  forall scalar,
    p8_utf8_scalar_wellformed scalar = true ->
    p8_h8_encode_scalar (p8_utf8_scalar_value scalar) = scalar.
Proof.
  intros scalar Valid.
  apply p8_h8_c1_value_injective_on_valid.
  - apply p8_h8_numeric_encoder_wellformed.
    now apply p8_h8_c1_valid_scalar_value.
  - exact Valid.
  - apply p8_h8_numeric_encoder_value.
Qed.

(* An actual C1 byte comparator theorem, not a native Text.Ord claim.
   Width changes imply different lead bytes and nonoverlapping scalar
   ranges. Within one width, the first differing base-64 digit decides
   the numeral; the 0..63 lower digits cannot reverse it. *)
Theorem p8_h8_scalar_bytes_numeric_compare :
  forall left right,
    p8_utf8_scalar_wellformed left = true ->
    p8_utf8_scalar_wellformed right = true ->
    p8_d2_compare_bytes
      (p8_utf8_scalar_bytes left)
      (p8_utf8_scalar_bytes right) =
    Nat.compare
      (p8_utf8_scalar_value left)
      (p8_utf8_scalar_value right).
Proof.
  intros left right ValidLeft ValidRight.
  pose proof (p8_h8_wellformed_width_bounds left ValidLeft)
    as LeftBounds.
  pose proof (p8_h8_wellformed_width_bounds right ValidRight)
    as RightBounds.
  destruct left as [a | a b | a b c | a b c d];
    destruct right as [u | u v | u v w | u v w x];
    cbn [p8_utf8_scalar_bytes p8_d2_compare_bytes
         p8_utf8_scalar_value] in *;
    cbn [p8_utf8_scalar_wellformed] in ValidLeft, ValidRight;
    unfold p8_octet_between in ValidLeft, ValidRight;
    p8_h8_unpack_octets;
    repeat (
      cbn [p8_d2_compare_bytes];
      match goal with
      | |- context [Nat.compare ?n ?m] =>
          let E := fresh "ByteCompare" in
          destruct (Nat.compare n m) eqn:E;
            [apply Nat.compare_eq_iff in E |
             apply Nat.compare_lt_iff in E |
             apply Nat.compare_gt_iff in E]
      end
    );
    cbn [p8_d2_compare_bytes];
    try reflexivity;
    try (exfalso; lia).
  Show.
Qed.

Theorem p8_h8_scalar_byte_less_iff :
  forall left right,
    p8_utf8_scalar_wellformed left = true ->
    p8_utf8_scalar_wellformed right = true ->
    (p8_d2_compare_bytes
      (p8_utf8_scalar_bytes left)
      (p8_utf8_scalar_bytes right) = Lt <->
     p8_utf8_scalar_value left < p8_utf8_scalar_value right).
Proof.
  intros left right VL VR.
  rewrite (p8_h8_scalar_bytes_numeric_compare left right VL VR).
  apply Nat.compare_lt_iff.
Qed.

Theorem p8_h8_scalar_byte_eq_iff :
  forall left right,
    p8_utf8_scalar_wellformed left = true ->
    p8_utf8_scalar_wellformed right = true ->
    (p8_d2_compare_bytes
      (p8_utf8_scalar_bytes left)
      (p8_utf8_scalar_bytes right) = Eq <-> left = right).
Proof.
  intros left right VL VR.
  rewrite (p8_h8_scalar_bytes_numeric_compare left right VL VR).
  rewrite Nat.compare_eq_iff.
  split; intro H.
  - now apply p8_h8_c1_value_injective_on_valid.
  - now subst.
Qed.

(* A list comparison consumes corresponding prefixes until the first
   differing octet. The following generic law needs equal prefix lengths;
   it is deliberately NOT asserted for arbitrary prefix-related byte lists. *)
Lemma p8_h8_byte_compare_equal_width_suffix :
  forall xs ys suffix1 suffix2,
    length xs = length ys ->
    p8_d2_compare_bytes (xs ++ suffix1) (ys ++ suffix2) =
    match p8_d2_compare_bytes xs ys with
    | Eq => p8_d2_compare_bytes suffix1 suffix2
    | other => other
    end.
Proof.
  induction xs as [|a xs IH]; intros ys suffix1 suffix2 SameLength;
    destruct ys as [|b ys]; simpl in SameLength;
    try discriminate.
  - reflexivity.
  - apply Nat.succ_inj in SameLength.
    simpl.
    destruct (Nat.compare a b) eqn:Compared; simpl;
      try reflexivity.
    now rewrite (IH ys suffix1 suffix2 SameLength).
Qed.

(* Strict UTF-8 lead-byte ranges separate all DIFFERENT widths. Even when
   the following suffix is arbitrary, it cannot decide their comparison. *)
Lemma p8_h8_scalar_byte_append :
  forall left right suffix1 suffix2,
    p8_utf8_scalar_wellformed left = true ->
    p8_utf8_scalar_wellformed right = true ->
    p8_d2_compare_bytes
      (p8_utf8_scalar_bytes left ++ suffix1)
      (p8_utf8_scalar_bytes right ++ suffix2) =
    match p8_d2_compare_bytes
      (p8_utf8_scalar_bytes left)
      (p8_utf8_scalar_bytes right) with
    | Eq => p8_d2_compare_bytes suffix1 suffix2
    | other => other
    end.
Proof.
  intros left right suffix1 suffix2 VL VR.
  destruct left as [a | a b | a b c | a b c d];
    destruct right as [u | u v | u v w | u v w x];
    cbn [p8_utf8_scalar_bytes];
    try (rewrite p8_h8_byte_compare_equal_width_suffix
           by reflexivity; reflexivity);
    cbn [p8_utf8_scalar_wellformed] in VL, VR;
    unfold p8_octet_between in VL, VR;
    p8_h8_unpack_octets;
    simpl;
    destruct (Nat.compare a u) eqn:Lead;
      try reflexivity;
    apply Nat.compare_eq_iff in Lead;
    lia.
Qed.

(* The scalar-stream comparison is a finite lexicographic comparison of
   NUMERIC Unicode code points, not an assumed Haskell Ord Text instance. *)
Fixpoint p8_h8_compare_scalar_values
  (xs ys : list P8Utf8ScalarOctets) {struct xs} : comparison :=
  match xs, ys with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: tail, y :: rest =>
      match Nat.compare (p8_utf8_scalar_value x)
                        (p8_utf8_scalar_value y) with
      | Eq => p8_h8_compare_scalar_values tail rest
      | other => other
      end
  end.

Theorem p8_h8_d1_stream_lex_numeric_compare :
  forall xs ys,
    p8_d1_valid xs = true ->
    p8_d1_valid ys = true ->
    p8_d2_compare_bytes (p8_d1_encode xs) (p8_d1_encode ys) =
    p8_h8_compare_scalar_values xs ys.
Proof.
  induction xs as [|a xs IH]; intros ys VL VR;
    destruct ys as [|b ys];
    cbn [p8_d1_encode p8_h8_compare_scalar_values] in *.
  - reflexivity.
  - destruct b; reflexivity.
  - destruct a; reflexivity.
  - unfold p8_d1_valid in VL, VR.
    cbn [forallb] in VL, VR.
    apply andb_true_iff in VL as [Va Vxs].
    apply andb_true_iff in VR as [Vb Vys].
    rewrite (p8_h8_scalar_byte_append
      a b (p8_d1_encode xs) (p8_d1_encode ys) Va Vb).
    rewrite (p8_h8_scalar_bytes_numeric_compare a b Va Vb).
    destruct (Nat.compare
      (p8_utf8_scalar_value a) (p8_utf8_scalar_value b));
      try reflexivity.
    now apply IH.
Qed.

Theorem p8_h8_d1_stream_strict_lex_iff :
  forall xs ys,
    p8_d1_valid xs = true ->
    p8_d1_valid ys = true ->
    (p8_d2_compare_bytes (p8_d1_encode xs) (p8_d1_encode ys) = Lt
      <-> p8_h8_compare_scalar_values xs ys = Lt).
Proof.
  intros xs ys VL VR.
  now rewrite (p8_h8_d1_stream_lex_numeric_compare xs ys VL VR).
Qed.

Example p8_h8_d1_empty_before_nonempty :
  p8_d2_compare_bytes (p8_d1_encode [])
    (p8_d1_encode [P8Utf8One 0]) = Lt.
Proof. reflexivity. Qed.
Example p8_h8_d1_proper_scalar_prefix :
  p8_d2_compare_bytes
    (p8_d1_encode [P8Utf8One 65])
    (p8_d1_encode [P8Utf8One 65; P8Utf8One 0]) = Lt.
Proof. reflexivity. Qed.
Example p8_h8_d1_equal_identical :
  p8_d2_compare_bytes
    (p8_d1_encode [P8Utf8One 65; P8Utf8Two 195 169])
    (p8_d1_encode [P8Utf8One 65; P8Utf8Two 195 169]) = Eq.
Proof. reflexivity. Qed.

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
Print Assumptions p8_h8_numeric_encoder_admitted.
Print Assumptions p8_h8_numeric_encoder_injective.
Print Assumptions p8_h8_wellformed_width_bounds.
Print Assumptions p8_h8_c1_value_injective_on_valid.
Print Assumptions p8_h8_encoder_c1_inverse.
Print Assumptions p8_h8_scalar_bytes_numeric_compare.
Print Assumptions p8_h8_scalar_byte_less_iff.
Print Assumptions p8_h8_scalar_byte_eq_iff.
Print Assumptions p8_h8_byte_compare_equal_width_suffix.
Print Assumptions p8_h8_scalar_byte_append.
Print Assumptions p8_h8_d1_stream_lex_numeric_compare.
Print Assumptions p8_h8_d1_stream_strict_lex_iff.
