From Coq Require Import List Bool Arith.PeanoNat Lia.
From Phil.Verification Require Import P8UnicodeUtf8Model.
Import ListNotations.

(*
  P8-D1: executable, strict UTF-8 stream model, independent of P9.
  Each element is a C1 canonical UTF-8 scalar-octet constructor. The
  accepted list domain is checked by forallb, not postulated as an axiom.
  These octet values are NOT Haskell Text or native source authority.
*)

Definition p8_d1_valid (scalars : list P8Utf8ScalarOctets) : bool :=
  forallb p8_utf8_scalar_wellformed scalars.

Fixpoint p8_d1_encode (scalars : list P8Utf8ScalarOctets) : list nat :=
  match scalars with
  | [] => []
  | one :: rest => p8_utf8_scalar_bytes one ++ p8_d1_encode rest
  end.

(* The first byte selects exactly one possible width. Every candidate is
   then rechecked against the full existing C1 strict scalar grammar. *)
Definition p8_d1_candidate (bytes : list nat)
  : option (P8Utf8ScalarOctets * list nat) :=
  match bytes with
  | [] => None
  | a :: rest =>
      if a <? 128 then Some (P8Utf8One a, rest)
      else if a <? 224 then
        match rest with
        | b :: tail => Some (P8Utf8Two a b, tail)
        | [] => None
        end
      else if a <? 240 then
        match rest with
        | b :: c :: tail => Some (P8Utf8Three a b c, tail)
        | _ => None
        end
      else
        match rest with
        | b :: c :: d :: tail => Some (P8Utf8Four a b c d, tail)
        | _ => None
        end
  end.

Definition p8_d1_decode_one (bytes : list nat)
  : option (P8Utf8ScalarOctets * list nat) :=
  match p8_d1_candidate bytes with
  | None => None
  | Some (one, rest) =>
      if p8_utf8_scalar_wellformed one then Some (one, rest) else None
  end.

(* Fuel is bounded by the number of source bytes. It is not an encoding of
   any native Phil ID. No successful parse may leave bytes unconsumed. *)
Fixpoint p8_d1_decode_fuel (fuel : nat) (bytes : list nat)
  : option (list P8Utf8ScalarOctets) :=
  match fuel, bytes with
  | _, [] => Some []
  | 0, _ :: _ => None
  | S remaining, _ :: _ =>
      match p8_d1_decode_one bytes with
      | None => None
      | Some (one, rest) =>
          match p8_d1_decode_fuel remaining rest with
          | None => None
          | Some more => Some (one :: more)
          end
      end
  end.

Definition p8_d1_decode (bytes : list nat)
  : option (list P8Utf8ScalarOctets) :=
  p8_d1_decode_fuel (length bytes) bytes.

Ltac p8_d1_lead_bounds :=
  (* Do not [simpl] the symbolic Nat.leb tests: doing so unfolds their
     recursion and hides the arithmetic inequalities from lia. *)
  match goal with
  | Hyp : p8_utf8_scalar_wellformed _ = true |- _ =>
      unfold p8_utf8_scalar_wellformed, p8_octet_between in Hyp
  end;
  repeat match goal with
    | Q : (_ && _) = true |- _ =>
        apply andb_true_iff in Q; destruct Q
    | Q : (_ <=? _) = true |- _ =>
        apply Nat.leb_le in Q
  end;
  lia.

Lemma p8_d1_candidate_prefix :
  forall s suffix,
    p8_utf8_scalar_wellformed s = true ->
    p8_d1_candidate (p8_utf8_scalar_bytes s ++ suffix) =
      Some (s, suffix).
Proof.
  intros s suffix H.
  destruct s as [a | a b | a b c | a b c d]; simpl.
  - assert (a <? 128 = true) as E
      by (apply Nat.ltb_lt; p8_d1_lead_bounds).
    rewrite E. reflexivity.
  - assert (a <? 128 = false) as E1
      by (apply Nat.ltb_ge; p8_d1_lead_bounds).
    assert (a <? 224 = true) as E2
      by (apply Nat.ltb_lt; p8_d1_lead_bounds).
    rewrite E1, E2. reflexivity.
  - assert (a <? 128 = false) as E1
      by (apply Nat.ltb_ge; p8_d1_lead_bounds).
    assert (a <? 224 = false) as E2
      by (apply Nat.ltb_ge; p8_d1_lead_bounds).
    assert (a <? 240 = true) as E3
      by (apply Nat.ltb_lt; p8_d1_lead_bounds).
    rewrite E1, E2, E3. reflexivity.
  - assert (a <? 128 = false) as E1
      by (apply Nat.ltb_ge; p8_d1_lead_bounds).
    assert (a <? 224 = false) as E2
      by (apply Nat.ltb_ge; p8_d1_lead_bounds).
    assert (a <? 240 = false) as E3
      by (apply Nat.ltb_ge; p8_d1_lead_bounds).
    rewrite E1, E2, E3. reflexivity.
Qed.

Lemma p8_d1_candidate_shape :
  forall bytes s suffix,
    p8_d1_candidate bytes = Some (s, suffix) ->
    bytes = p8_utf8_scalar_bytes s ++ suffix.
Proof.
  intros [|a xs] s suffix H; simpl in H; try discriminate.
  destruct (a <? 128) eqn:E1.
  - inversion H; subst; reflexivity.
  - destruct (a <? 224) eqn:E2.
    + destruct xs as [|b ys]; simpl in H; try discriminate.
      inversion H; subst; reflexivity.
    + destruct (a <? 240) eqn:E3.
      * destruct xs as [|b ys]; try discriminate.
        destruct ys as [|c zs]; try discriminate.
        simpl in H. inversion H; subst; reflexivity.
      * destruct xs as [|b ys]; try discriminate.
        destruct ys as [|c zs]; try discriminate.
        destruct zs as [|d ws]; try discriminate.
        simpl in H. inversion H; subst; reflexivity.
Qed.

Lemma p8_d1_decode_one_prefix :
  forall s suffix,
    p8_utf8_scalar_wellformed s = true ->
    p8_d1_decode_one (p8_utf8_scalar_bytes s ++ suffix) =
      Some (s, suffix).
Proof.
  intros s suffix H.
  unfold p8_d1_decode_one.
  rewrite p8_d1_candidate_prefix by exact H.
  rewrite H. reflexivity.
Qed.

Lemma p8_d1_decode_one_sound :
  forall bytes s suffix,
    p8_d1_decode_one bytes = Some (s, suffix) ->
    p8_utf8_scalar_wellformed s = true /\
    bytes = p8_utf8_scalar_bytes s ++ suffix.
Proof.
  intros bytes s suffix H.
  unfold p8_d1_decode_one in H.
  destruct (p8_d1_candidate bytes) as [[one rest]|] eqn:E;
    try discriminate.
  destruct (p8_utf8_scalar_wellformed one) eqn:W;
    try discriminate.
  inversion H; subst.
  split; [exact W|].
  eapply p8_d1_candidate_shape; eassumption.
Qed.

Lemma p8_d1_decode_fuel_step :
  forall s suffix fuel,
    p8_utf8_scalar_wellformed s = true ->
    p8_d1_decode_fuel (S fuel)
      (p8_utf8_scalar_bytes s ++ suffix) =
    match p8_d1_decode_fuel fuel suffix with
    | Some rest => Some (s :: rest)
    | None => None
    end.
Proof.
  intros s suffix fuel H.
  destruct s;
    cbn [p8_utf8_scalar_bytes app p8_d1_decode_fuel];
    rewrite (p8_d1_decode_one_prefix _ _ H);
    destruct (p8_d1_decode_fuel fuel suffix); reflexivity.
Qed.

Lemma p8_d1_fuel_roundtrip :
  forall scalars extra,
    p8_d1_valid scalars = true ->
    p8_d1_decode_fuel (length scalars + extra)
      (p8_d1_encode scalars) = Some scalars.
Proof.
  induction scalars as [|s rest IH]; intros extra H.
  - reflexivity.
  - unfold p8_d1_valid in H. simpl in H.
    apply andb_true_iff in H as [Ws Wrest].
    change
      (p8_d1_decode_fuel (S (length rest + extra))
        (p8_utf8_scalar_bytes s ++ p8_d1_encode rest) =
       Some (s :: rest)).
    rewrite p8_d1_decode_fuel_step by exact Ws.
    rewrite (IH extra Wrest). reflexivity.
Qed.

Lemma p8_d1_scalar_bytes_nonempty :
  forall s, 1 <= length (p8_utf8_scalar_bytes s).
Proof. destruct s; simpl; lia. Qed.

Lemma p8_d1_encoded_length :
  forall scalars, length scalars <= length (p8_d1_encode scalars).
Proof.
  induction scalars as [|s rest IH].
  - simpl; lia.
  - simpl. rewrite app_length.
    pose proof (p8_d1_scalar_bytes_nonempty s). lia.
Qed.

Theorem p8_d1_stream_roundtrip :
  forall scalars,
    p8_d1_valid scalars = true ->
    p8_d1_decode (p8_d1_encode scalars) = Some scalars.
Proof.
  intros scalars H.
  unfold p8_d1_decode.
  pose proof (p8_d1_encoded_length scalars) as E.
  replace (length (p8_d1_encode scalars))
    with (length scalars +
      (length (p8_d1_encode scalars) - length scalars)) by lia.
  apply p8_d1_fuel_roundtrip. exact H.
Qed.

Lemma p8_d1_decode_fuel_sound :
  forall fuel bytes scalars,
    p8_d1_decode_fuel fuel bytes = Some scalars ->
    p8_d1_valid scalars = true /\
    p8_d1_encode scalars = bytes.
Proof.
  induction fuel as [|fuel IH]; intros bytes scalars H.
  - destruct bytes as [|a tail];
      cbn [p8_d1_decode_fuel] in H.
    + inversion H; subst; split; reflexivity.
    + discriminate.
  - destruct bytes as [|a tail];
      cbn [p8_d1_decode_fuel] in H.
    + inversion H; subst; split; reflexivity.
    + destruct (p8_d1_decode_one (a :: tail))
        as [[s rest]|] eqn:Step; try discriminate.
      destruct (p8_d1_decode_fuel fuel rest)
        as [more|] eqn:Rest; try discriminate.
      inversion H; subst; clear H.
      apply p8_d1_decode_one_sound in Step as [Ws Shape].
      apply IH in Rest as [Wmore Enc].
      split.
      * unfold p8_d1_valid in *. simpl.
        rewrite Ws, Wmore. reflexivity.
      * simpl. rewrite Enc. symmetry. exact Shape.
Qed.

Theorem p8_d1_stream_canonical_acceptance :
  forall bytes scalars,
    p8_d1_decode bytes = Some scalars ->
    p8_d1_valid scalars = true /\
    p8_d1_encode scalars = bytes.
Proof.
  intros bytes scalars H.
  unfold p8_d1_decode in H.
  eapply p8_d1_decode_fuel_sound; eassumption.
Qed.

Theorem p8_d1_stream_injective :
  forall left right,
    p8_d1_valid left = true ->
    p8_d1_valid right = true ->
    p8_d1_encode left = p8_d1_encode right ->
    left = right.
Proof.
  intros left right HL HR Equal.
  pose proof (p8_d1_stream_roundtrip left HL) as L.
  pose proof (p8_d1_stream_roundtrip right HR) as R.
  rewrite Equal in L. rewrite R in L.
  now inversion L.
Qed.

Theorem p8_d1_encode_concat :
  forall left right,
    p8_d1_encode (left ++ right) =
      p8_d1_encode left ++ p8_d1_encode right.
Proof.
  induction left as [|s tail IH]; intros right; simpl.
  - reflexivity.
  - rewrite IH, app_assoc. reflexivity.
Qed.

Theorem p8_d1_canonical_concat_parse :
  forall left right,
    p8_d1_valid left = true ->
    p8_d1_valid right = true ->
    p8_d1_decode (p8_d1_encode left ++ p8_d1_encode right) =
      Some (left ++ right).
Proof.
  intros left right HL HR.
  rewrite <- p8_d1_encode_concat.
  apply p8_d1_stream_roundtrip.
  unfold p8_d1_valid in *.
  rewrite forallb_app, HL, HR. reflexivity.
Qed.

Theorem p8_d1_unique_stream_parse :
  forall bytes left right,
    p8_d1_decode bytes = Some left ->
    p8_d1_decode bytes = Some right ->
    left = right.
Proof. intros; congruence. Qed.

Example p8_d1_empty :
  p8_d1_decode [] = Some [].
Proof. reflexivity. Qed.
Example p8_d1_nul_multiscalar :
  p8_d1_decode [120;0;121] =
    Some [P8Utf8One 120; P8Utf8One 0; P8Utf8One 121].
Proof. reflexivity. Qed.
Example p8_d1_mixed_utf8 :
  p8_d1_decode [195;169;240;159;153;130;244;143;191;191] =
    Some [P8Utf8Two 195 169;
          P8Utf8Four 240 159 153 130;
          P8Utf8Four 244 143 191 191].
Proof. reflexivity. Qed.
Example p8_d1_composed_decomposed_distinct :
  p8_d1_decode [195;169] <>
    p8_d1_decode [101;204;129].
Proof. discriminate. Qed.
Example p8_d1_reject_truncated_suffix :
  p8_d1_decode [65;240;159;153] = None.
Proof. reflexivity. Qed.
Example p8_d1_reject_overlong_middle :
  p8_d1_decode [65;192;128;66] = None.
Proof. reflexivity. Qed.
Example p8_d1_reject_surrogate_middle :
  p8_d1_decode [65;237;160;128;66] = None.
Proof. reflexivity. Qed.
Example p8_d1_reject_out_of_range :
  p8_d1_decode [244;144;128;128] = None.
Proof. reflexivity. Qed.
Example p8_d1_reject_bad_continuation :
  p8_d1_decode [65;226;40;161] = None.
Proof. reflexivity. Qed.
Example p8_d1_reject_invalid_trailing :
  p8_d1_decode [65;128] = None.
Proof. reflexivity. Qed.
Example p8_d1_reject_octet_outside_byte_range :
  p8_d1_decode [65;256] = None.
Proof. reflexivity. Qed.
(* A well-formed extra trailing scalar is a second character, not junk.
   Exact scalar parsing, unlike stream parsing, rejects such a suffix. *)
Example p8_d1_valid_trailing_scalar_is_second_character :
  p8_d1_decode [0;0] = Some [P8Utf8One 0; P8Utf8One 0].
Proof. reflexivity. Qed.

Print Assumptions p8_d1_stream_roundtrip.
Print Assumptions p8_d1_stream_canonical_acceptance.
Print Assumptions p8_d1_stream_injective.
Print Assumptions p8_d1_encode_concat.
Print Assumptions p8_d1_canonical_concat_parse.
Print Assumptions p8_d1_unique_stream_parse.
