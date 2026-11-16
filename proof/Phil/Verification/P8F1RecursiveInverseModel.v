From Coq Require Import List Bool Arith.PeanoNat Lia.
From Phil.Verification Require Import
  P8D1UnicodeStreamModel P8D2StructuralOrderModel
  P8E1CanonicalWireModel P8E2CanonicalApplicationModel.
Import ListNotations.

(*
 P8-F1: first independent inversion lemmas against the actual immutable
 E1 executable scanner, not a replacement parser. This file is an active
 proof development. Until the universal form inversion theorem compiles,
 it cannot discharge P8-F1 or authorize a protected merge.
*)

Fixpoint p8_f1_digit_value (acc : nat) (digits : list nat) : nat :=
  match digits with
  | [] => acc
  | b :: rest => p8_f1_digit_value (acc * 10 + (b - 48)) rest
  end.

Lemma p8_f1_digit_value_append :
  forall left right acc,
    p8_f1_digit_value acc (left ++ right) =
    p8_f1_digit_value (p8_f1_digit_value acc left) right.
Proof.
  induction left as [|b rest IH]; intros right acc; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma p8_f1_digit_offset :
  forall n, n < 10 -> p8_e1_digit (48 + n) = true.
Proof.
  intros n H.
  unfold p8_e1_digit.
  apply andb_true_iff. split; apply Nat.leb_le; lia.
Qed.

Lemma p8_f1_count_scan_suffix :
  forall digits suffix acc used,
    0 < used ->
    forallb p8_e1_digit digits = true ->
    p8_e1_count_scan (digits ++ 58 :: suffix) acc used false =
       Some (p8_f1_digit_value acc digits, suffix).
Proof.
  induction digits as [|b rest IH]; intros suffix acc used Hused Hdigits.
  - simpl.
    assert ((used =? 0) = false) as E by (apply Nat.eqb_neq; lia).
    rewrite E. reflexivity.
  - simpl in Hdigits.
    apply andb_true_iff in Hdigits as [Digit Rest].
    simpl [app p8_e1_count_scan p8_f1_digit_value].
    assert (NotColon : (b =? 58) = false).
    { apply Nat.eqb_neq.
      unfold p8_e1_digit in Digit.
      apply andb_true_iff in Digit as [Lower Upper].
      apply Nat.leb_le in Upper. lia. }
    rewrite NotColon, Digit.
    assert (Already : (used =? 0) = false)
      by (apply Nat.eqb_neq; lia).
    rewrite Already. simpl.
    apply IH; [lia|exact Rest].
Qed.

(*
 A nonempty ASCII decimal digit sequence has the expected unbounded
 accumulator semantics, provided leading zero occurs only for the
 singleton representation of zero. This states precisely the E1 count
 scanner's prefix/remainder law, without assuming its result as a Prop.
*)
Theorem p8_f1_read_canonical_digits :
  forall first rest suffix,
    p8_e1_digit first = true ->
    forallb p8_e1_digit rest = true ->
    (rest = [] \/ first <> 48) ->
    p8_e1_read_count ((first :: rest) ++ 58 :: suffix) =
      Some (p8_f1_digit_value 0 (first :: rest), suffix).
Proof.
  intros first rest suffix D R Canonical.
  unfold p8_e1_read_count.
  simpl [app p8_e1_count_scan p8_f1_digit_value].
  assert (Colon : (first =? 58) = false).
  { apply Nat.eqb_neq.
    unfold p8_e1_digit in D.
    apply andb_true_iff in D as [_ Upper].
    apply Nat.leb_le in Upper. lia. }
  rewrite Colon, D.
  destruct rest as [|next tail].
  - simpl [app p8_e1_count_scan p8_f1_digit_value].
    reflexivity.
  - assert (NZ : first <> 48).
    { destruct Canonical as [Impossible | Nonzero];
        [discriminate | exact Nonzero]. }
    assert (NotZero : (first =? 48) = false).
    { apply Nat.eqb_neq. exact NZ. }
    rewrite NotZero.
    (* Keep the tail abstract: simplifying the next digit's scanner test
       destroys the direct match with the general suffix lemma. *)
    change (p8_e1_count_scan ((next :: tail) ++ 58 :: suffix)
              (first - 48) 1 false =
            Some (p8_f1_digit_value (first - 48) (next :: tail), suffix)).
    apply p8_f1_count_scan_suffix; [lia|exact R].
Qed.

(* Every digit produced by the actual E1 encoder is a decimal octet.
   The missing stronger numeral inversion additionally needs the full
   quotient/remainder and first-digit proof. *)
Lemma p8_f1_decimal_fuel_digits :
  forall fuel n,
    forallb p8_e1_digit (p8_e1_decimal_fuel fuel n) = true.
Proof.
  induction fuel as [|fuel IH]; intro n.
  - change (p8_e1_digit (48 + n mod 10) && true = true).
    rewrite Bool.andb_true_r.
    apply p8_f1_digit_offset.
    apply Nat.mod_upper_bound; lia.
  - cbn [p8_e1_decimal_fuel].
    destruct (n <? 10) eqn:Small.
    + apply Nat.ltb_lt in Small.
      change (p8_e1_digit (48 + n) && true = true).
      rewrite Bool.andb_true_r.
      apply p8_f1_digit_offset. lia.
    + rewrite forallb_app.
      change
        (forallb p8_e1_digit (p8_e1_decimal_fuel fuel (n / 10)) &&
         (p8_e1_digit (48 + n mod 10) && true) = true).
      rewrite IH, Bool.andb_true_l, Bool.andb_true_r.
      apply p8_f1_digit_offset.
      apply Nat.mod_upper_bound; lia.
Qed.

(* The emitter's fuel is a bound on the natural count, never a
   fabricated identity for Phil Text. Decimal division decreases under
   this bound, so every emitted count represents the original natural. *)
Lemma p8_f1_decimal_fuel_value :
  forall fuel n, n <= fuel ->
    p8_f1_digit_value 0 (p8_e1_decimal_fuel fuel n) = n.
Proof.
  induction fuel as [|fuel IH]; intros n Bound.
  - assert (n = 0) by lia. subst n. reflexivity.
  - cbn [p8_e1_decimal_fuel].
    destruct (n <? 10) eqn:Small.
    + apply Nat.ltb_lt in Small.
      cbn [p8_f1_digit_value]. lia.
    + apply Nat.ltb_ge in Small.
      pose proof (Nat.div_mod n 10 ltac:(lia)) as Division.
      pose proof (Nat.mod_upper_bound n 10 ltac:(lia)) as Remainder.
      assert (QuotientBound : n / 10 <= fuel) by lia.
      rewrite p8_f1_digit_value_append.
      rewrite (IH (n / 10) QuotientBound).
      cbn [p8_f1_digit_value].
      lia.
Qed.

Lemma p8_f1_decimal_fuel_canonical :
  forall fuel n, n <= fuel ->
    exists first rest,
      p8_e1_decimal_fuel fuel n = first :: rest /\
      (n = 0 -> first = 48 /\ rest = []) /\
      (0 < n -> first <> 48).
Proof.
  induction fuel as [|fuel IH]; intros n Bound.
  - assert (n = 0) by lia. subst n.
    exists 48, []. split; [reflexivity|split].
    + intro _. split; reflexivity.
    + lia.
  - cbn [p8_e1_decimal_fuel].
    destruct (n <? 10) eqn:Small.
    + exists (48 + n), []. split; [reflexivity|split].
      * intro Zero. subst n. split; reflexivity.
      * intros Pos. lia.
    + apply Nat.ltb_ge in Small.
      pose proof (Nat.div_mod n 10 ltac:(lia)) as Division.
      pose proof (Nat.mod_upper_bound n 10 ltac:(lia)) as Remainder.
      assert (QuotientBound : n / 10 <= fuel) by lia.
      destruct (IH (n / 10) QuotientBound)
        as [first [rest [Shape [Zero Nonzero]]]].
      exists first, (rest ++ [48 + n mod 10]).
      rewrite Shape. simpl [app].
      split; [reflexivity|split].
      * intros Impossible. lia.
      * intros _. apply Nonzero. lia.
Qed.

Theorem p8_f1_frame_count_roundtrip :
  forall n suffix,
    p8_e1_read_count (p8_e1_frame_count n ++ suffix) =
      Some (n, suffix).
Proof.
  intros n suffix.
  unfold p8_e1_frame_count, p8_e1_decimal.
  rewrite app_assoc. simpl [app].
  destruct (p8_f1_decimal_fuel_canonical (S n) n)
    as [first [rest [Shape [Zero Nonzero]]]]; [lia|].
  pose proof (p8_f1_decimal_fuel_digits (S n) n) as Digits.
  rewrite Shape in Digits. simpl in Digits.
  apply andb_true_iff in Digits as [First Rest].
  assert (Canonical : rest = [] \/ first <> 48).
  { destruct (Nat.eq_dec n 0) as [IsZero|NotZero].
    - left. destruct (Zero IsZero) as [_ IsEmpty]. exact IsEmpty.
    - right. apply Nonzero. lia. }
  rewrite Shape.
  rewrite (p8_f1_read_canonical_digits first rest suffix
             First Rest Canonical).
  rewrite <- Shape.
  rewrite (p8_f1_decimal_fuel_value (S n) n) by lia.
  reflexivity.
Qed.

Theorem p8_f1_text_prefix_roundtrip :
  forall txt suffix,
    p8_d2_text_valid txt = true ->
    p8_e1_parse_text (p8_e1_put_text txt ++ suffix) =
      Some (txt, suffix).
Proof.
  intros txt suffix Valid.
  unfold p8_e1_put_text.
  replace ((116 :: p8_e1_frame_count (length txt) ++ txt) ++ suffix)
    with (116 :: (p8_e1_frame_count (length txt) ++ (txt ++ suffix)))
    by (simpl [app]; rewrite app_assoc; reflexivity).
  cbn [p8_e1_parse_text].
  rewrite p8_f1_frame_count_roundtrip.
  rewrite p8_e1_take_exact_prefix.
  rewrite Valid. reflexivity.
Qed.

Lemma p8_f1_decoder_is_exact_on_a_success :
  forall wire form,
    p8_e2_normalize_form wire = Some form ->
    p8_d2_valid_form form = true /\
    p8_e1_put_form form = wire.
Proof.
  intros wire form H.
  apply p8_e2_normalized_form_sound in H as [_ [V E]].
  auto.
Qed.

Print Assumptions p8_f1_digit_value_append.
Print Assumptions p8_f1_count_scan_suffix.
Print Assumptions p8_f1_read_canonical_digits.
Print Assumptions p8_f1_decimal_fuel_digits.
Print Assumptions p8_f1_decimal_fuel_value.
Print Assumptions p8_f1_decimal_fuel_canonical.
Print Assumptions p8_f1_frame_count_roundtrip.
Print Assumptions p8_f1_text_prefix_roundtrip.
Print Assumptions p8_f1_decoder_is_exact_on_a_success.
