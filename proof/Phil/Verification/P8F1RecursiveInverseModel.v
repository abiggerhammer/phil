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
    + intro Ignored. split; reflexivity.
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
      * intros Positive. apply Nonzero. lia.
Qed.

Theorem p8_f1_frame_count_roundtrip :
  forall n suffix,
    p8_e1_read_count (p8_e1_frame_count n ++ suffix) =
      Some (n, suffix).
Proof.
  intros n suffix.
  assert (Frame :
    p8_e1_frame_count n ++ suffix =
      p8_e1_decimal_fuel (S n) n ++ 58 :: suffix).
  { unfold p8_e1_frame_count, p8_e1_decimal.
    symmetry. exact (app_assoc (p8_e1_decimal_fuel (S n) n) [58] suffix). }
  rewrite Frame.
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

(* Every finite structural emitter contributes a constructor octet.  These
   length bounds justify E1's declared collection-cardinality guard for
   canonical encodings, independently of parser success assumptions. *)
Lemma p8_f1_put_form_has_tag :
  forall form, 0 < length (p8_e1_put_form form).
Proof.
  intros [txt|xs|xs|xs]; cbn [p8_e1_put_form length]; lia.
Qed.

Lemma p8_f1_put_text_has_tag :
  forall txt, 0 < length (p8_e1_put_text txt).
Proof.
  intros txt. unfold p8_e1_put_text. simpl. lia.
Qed.

Theorem p8_f1_forms_count_fits_canonical_wire :
  forall xs suffix,
    p8_e1_forms_count xs <= length (p8_e1_put_forms xs ++ suffix).
Proof.
  induction xs as [|form rest IH]; intros suffix.
  - cbn [p8_e1_forms_count p8_e1_put_forms]. lia.
  - cbn [p8_e1_forms_count p8_e1_put_forms].
    repeat rewrite app_length.
    specialize (IH suffix).
    rewrite app_length in IH.
    pose proof (p8_f1_put_form_has_tag form).
    lia.
Qed.

Theorem p8_f1_fields_count_fits_canonical_wire :
  forall fields suffix,
    p8_e1_fields_count fields <= length (p8_e1_put_fields fields ++ suffix).
Proof.
  induction fields as [|key value rest IH]; intros suffix.
  - cbn [p8_e1_fields_count p8_e1_put_fields]. lia.
  - cbn [p8_e1_fields_count p8_e1_put_fields].
    repeat rewrite app_length.
    specialize (IH suffix).
    rewrite app_length in IH.
    pose proof (p8_f1_put_text_has_tag key).
    pose proof (p8_f1_put_form_has_tag value).
    lia.
Qed.


(*
 These are genuine general prefix inverses for the atom and zero-arity
 constructor cases, not replacements for E1's parser. They establish the
 base cases needed by the still-outstanding mutual structural induction.
 The fuel is explicit, and the proofs use E1's actual executable parser.
*)
Theorem p8_f1_atom_prefix_all_fuel :
  forall fuel txt suffix,
    p8_d2_text_valid txt = true ->
    p8_e1_parse_form_fuel (S fuel)
      (p8_e1_put_form (P8D2Atom txt) ++ suffix) =
    Some (P8D2Atom txt, suffix).
Proof.
  intros fuel txt suffix Valid.
  change
    (match p8_e1_parse_text (p8_e1_put_text txt ++ suffix) with
     | Some (parsed, remaining) => Some (P8D2Atom parsed, remaining)
     | None => None
     end = Some (P8D2Atom txt, suffix)).
  rewrite (p8_f1_text_prefix_roundtrip txt suffix Valid).
  reflexivity.
Qed.

Theorem p8_f1_empty_ordered_prefix :
  forall fuel suffix,
    p8_e1_parse_form_fuel (S fuel)
      (p8_e1_put_form (P8D2Ordered P8D2Nil) ++ suffix) =
    Some (P8D2Ordered P8D2Nil, suffix).
Proof. intros fuel suffix; reflexivity. Qed.

Theorem p8_f1_empty_unordered_prefix :
  forall fuel suffix,
    p8_e1_parse_form_fuel (S fuel)
      (p8_e1_put_form (P8D2Unordered P8D2Nil) ++ suffix) =
    Some (P8D2Unordered P8D2Nil, suffix).
Proof. intros fuel suffix; reflexivity. Qed.

Theorem p8_f1_empty_record_prefix :
  forall fuel suffix,
    p8_e1_parse_form_fuel (S fuel)
      (p8_e1_put_form (P8D2Record P8D2FieldNil) ++ suffix) =
    Some (P8D2Record P8D2FieldNil, suffix).
Proof. intros fuel suffix; reflexivity. Qed.

Theorem p8_f1_atom_decode_roundtrip :
  forall txt,
    p8_d2_text_valid txt = true ->
    p8_e1_decode_form (p8_e1_put_form (P8D2Atom txt)) =
    Some (P8D2Atom txt).
Proof.
  intros txt Valid.
  pose proof
    (p8_f1_atom_prefix_all_fuel
      (length (p8_e1_put_form (P8D2Atom txt))) txt [] Valid)
    as Prefix.
  rewrite app_nil_r in Prefix.
  unfold p8_e1_decode_form, p8_e1_parse_form_prefix.
  rewrite Prefix. reflexivity.
Qed.

Theorem p8_f1_atom_trailing_rejected :
  forall txt trailing,
    p8_d2_text_valid txt = true ->
    trailing <> [] ->
    p8_e1_decode_form
      (p8_e1_put_form (P8D2Atom txt) ++ trailing) = None.
Proof.
  intros txt trailing Valid Nonempty.
  unfold p8_e1_decode_form, p8_e1_parse_form_prefix.
  rewrite (p8_f1_atom_prefix_all_fuel
    (length (p8_e1_put_form (P8D2Atom txt) ++ trailing))
    txt trailing Valid).
  destruct trailing as [|b rest]; [contradiction|reflexivity].
Qed.

Theorem p8_f1_atom_wire_injective :
  forall x y,
    p8_d2_text_valid x = true ->
    p8_d2_text_valid y = true ->
    p8_e1_put_form (P8D2Atom x) =
    p8_e1_put_form (P8D2Atom y) ->
    x = y.
Proof.
  intros x y ValidX ValidY Wire.
  pose proof (p8_f1_atom_decode_roundtrip x ValidX) as X.
  pose proof (p8_f1_atom_decode_roundtrip y ValidY) as Y.
  rewrite Wire in X. rewrite Y in X.
  congruence.
Qed.


(*
 E1's two local recursive count-loops are exposed here as transparent
 proof-only aliases. Their bodies are intentionally identical to E1's
 parse_forms/parse_fields closures; the subsequent proof must relate
 these loops to the *unchanged* E1 parser by kernel conversion, not by
 a caller-provided parser-correspondence axiom.
*)
Fixpoint p8_f1_forms_loop (fuel count : nat) (wire : list nat)
    : option (P8D2Forms * list nat) :=
  match count with
  | 0 => Some (P8D2Nil, wire)
  | S remaining =>
      match p8_e1_parse_form_fuel fuel wire with
      | None => None
      | Some (child, next) =>
          match p8_f1_forms_loop fuel remaining next with
          | None => None
          | Some (children, suffix) =>
              Some (P8D2Cons child children, suffix)
          end
      end
  end.

Fixpoint p8_f1_fields_loop (fuel count : nat) (wire : list nat)
    : option (P8D2Fields * list nat) :=
  match count with
  | 0 => Some (P8D2FieldNil, wire)
  | S remaining =>
      match p8_e1_parse_text wire with
      | None => None
      | Some (key, after_key) =>
          match p8_e1_parse_form_fuel fuel after_key with
          | None => None
          | Some (value, after_value) =>
              match p8_f1_fields_loop fuel remaining after_value with
              | None => None
              | Some (fields, suffix) =>
                  Some (P8D2FieldCons key value fields, suffix)
              end
          end
      end
  end.

Lemma p8_f1_forms_loop_complete_from_children :
  forall fuel,
    (forall form suffix,
      p8_d2_valid_form form = true ->
      length (p8_e1_put_form form) <= fuel ->
      p8_e1_parse_form_fuel fuel
        (p8_e1_put_form form ++ suffix) = Some (form, suffix)) ->
    forall xs suffix,
      p8_d2_valid_forms xs = true ->
      length (p8_e1_put_forms xs) <= fuel ->
      p8_f1_forms_loop fuel (p8_e1_forms_count xs)
        (p8_e1_put_forms xs ++ suffix) = Some (xs, suffix).
Proof.
  intros fuel Child xs.
  induction xs as [|form rest IH]; intros suffix Valid Bound.
  - reflexivity.
  - cbn [p8_d2_valid_forms] in Valid.
    apply andb_true_iff in Valid as [ValidForm ValidRest].
    assert (BoundForm : length (p8_e1_put_form form) <= fuel).
    { cbn [p8_e1_put_forms] in Bound.
      rewrite app_length in Bound. lia. }
    assert (BoundRest : length (p8_e1_put_forms rest) <= fuel).
    { cbn [p8_e1_put_forms] in Bound.
      rewrite app_length in Bound. lia. }
    cbn [p8_f1_forms_loop p8_e1_forms_count p8_e1_put_forms].
    rewrite app_assoc.
    rewrite (Child form (p8_e1_put_forms rest ++ suffix)
                   ValidForm BoundForm).
    rewrite (IH suffix ValidRest BoundRest).
    reflexivity.
Qed.

Lemma p8_f1_fields_loop_complete_from_children :
  forall fuel,
    (forall form suffix,
      p8_d2_valid_form form = true ->
      length (p8_e1_put_form form) <= fuel ->
      p8_e1_parse_form_fuel fuel
        (p8_e1_put_form form ++ suffix) = Some (form, suffix)) ->
    forall fields suffix,
      p8_d2_valid_fields fields = true ->
      length (p8_e1_put_fields fields) <= fuel ->
      p8_f1_fields_loop fuel (p8_e1_fields_count fields)
        (p8_e1_put_fields fields ++ suffix) = Some (fields, suffix).
Proof.
  intros fuel Child fields.
  induction fields as [|key value rest IH]; intros suffix Valid Bound.
  - reflexivity.
  - cbn [p8_d2_valid_fields] in Valid.
    destruct (p8_d2_text_valid key) eqn:ValidKey;
    destruct (p8_d2_valid_form value) eqn:ValidValue;
    destruct (p8_d2_valid_fields rest) eqn:ValidRest;
      simpl in Valid; try discriminate.
    assert (BoundValue : length (p8_e1_put_form value) <= fuel).
    { cbn [p8_e1_put_fields] in Bound.
      repeat rewrite app_length in Bound. lia. }
    assert (BoundRest : length (p8_e1_put_fields rest) <= fuel).
    { cbn [p8_e1_put_fields] in Bound.
      repeat rewrite app_length in Bound. lia. }
    cbn [p8_f1_fields_loop p8_e1_fields_count p8_e1_put_fields].
    repeat rewrite app_assoc.
    rewrite (p8_f1_text_prefix_roundtrip key
      (p8_e1_put_form value ++ p8_e1_put_fields rest ++ suffix)
      ValidKey).
    rewrite (Child value (p8_e1_put_fields rest ++ suffix)
      ValidValue BoundValue).
    rewrite (IH suffix ValidRest BoundRest).
    reflexivity.
Qed.


(*
 Main F1 induction on the parser's *actual fuel*. The inductive invariant
 is byte-size bounded: the outer constructor contributes at least one
 octet, so every nested child fits the strictly smaller parser fuel.
 The list/field lemmas above prove the E1 count loops from this invariant.
 The following 'change' goals rely on definitional conversion of those
 aliases with E1's original local recursors, not an assumed equivalence.
*)
Theorem p8_f1_form_prefix_fuel_bound :
  forall fuel form suffix,
    p8_d2_valid_form form = true ->
    length (p8_e1_put_form form) <= fuel ->
    p8_e1_parse_form_fuel fuel
      (p8_e1_put_form form ++ suffix) = Some (form, suffix).
Proof.
  induction fuel as [|fuel IH]; intros form suffix Valid Bound.
  - pose proof (p8_f1_put_form_has_tag form). lia.
  - destruct form as [txt|xs|xs|fields].
    + apply p8_f1_atom_prefix_all_fuel. exact Valid.
    + cbn [p8_d2_valid_form] in Valid.
      assert (ListBound : length (p8_e1_put_forms xs) <= fuel).
      { cbn [p8_e1_put_form] in Bound.
        repeat rewrite app_length in Bound. simpl in Bound. lia. }
      assert (Guard :
        (p8_e1_forms_count xs <=?
         length (p8_e1_put_forms xs ++ suffix)) = true).
      { apply Nat.leb_le.
        apply p8_f1_forms_count_fits_canonical_wire. }
      change
        (match p8_e1_read_count
          (p8_e1_frame_count (p8_e1_forms_count xs) ++
            (p8_e1_put_forms xs ++ suffix)) with
         | None => None
         | Some (n, after) =>
             if n <=? length after then
               match p8_f1_forms_loop fuel n after with
               | None => None
               | Some (parsed, trailing) =>
                   Some (P8D2Ordered parsed, trailing)
               end
             else None
         end = Some (P8D2Ordered xs, suffix)).
      rewrite p8_f1_frame_count_roundtrip, Guard.
      rewrite (p8_f1_forms_loop_complete_from_children
        fuel IH xs suffix Valid ListBound).
      reflexivity.
    + cbn [p8_d2_valid_form] in Valid.
      apply andb_true_iff in Valid as [Strict ValidChildren].
      assert (ListBound : length (p8_e1_put_forms xs) <= fuel).
      { cbn [p8_e1_put_form] in Bound.
        repeat rewrite app_length in Bound. simpl in Bound. lia. }
      assert (Guard :
        (p8_e1_forms_count xs <=?
         length (p8_e1_put_forms xs ++ suffix)) = true).
      { apply Nat.leb_le.
        apply p8_f1_forms_count_fits_canonical_wire. }
      change
        (match p8_e1_read_count
          (p8_e1_frame_count (p8_e1_forms_count xs) ++
            (p8_e1_put_forms xs ++ suffix)) with
         | None => None
         | Some (n, after) =>
             if n <=? length after then
               match p8_f1_forms_loop fuel n after with
               | None => None
               | Some (parsed, trailing) =>
                   if p8_d2_strict_members parsed &&
                      p8_d2_valid_forms parsed then
                     Some (P8D2Unordered parsed, trailing)
                   else None
               end
             else None
         end = Some (P8D2Unordered xs, suffix)).
      rewrite p8_f1_frame_count_roundtrip, Guard.
      rewrite (p8_f1_forms_loop_complete_from_children
        fuel IH xs suffix ValidChildren ListBound).
      rewrite Strict, ValidChildren. reflexivity.
    + cbn [p8_d2_valid_form] in Valid.
      apply andb_true_iff in Valid as [Strict ValidFields].
      assert (ListBound : length (p8_e1_put_fields fields) <= fuel).
      { cbn [p8_e1_put_form] in Bound.
        repeat rewrite app_length in Bound. simpl in Bound. lia. }
      assert (Guard :
        (p8_e1_fields_count fields <=?
         length (p8_e1_put_fields fields ++ suffix)) = true).
      { apply Nat.leb_le.
        apply p8_f1_fields_count_fits_canonical_wire. }
      change
        (match p8_e1_read_count
          (p8_e1_frame_count (p8_e1_fields_count fields) ++
            (p8_e1_put_fields fields ++ suffix)) with
         | None => None
         | Some (n, after) =>
             if n <=? length after then
               match p8_f1_fields_loop fuel n after with
               | None => None
               | Some (parsed, trailing) =>
                   if p8_d2_strict_keys parsed &&
                      p8_d2_valid_fields parsed then
                     Some (P8D2Record parsed, trailing)
                   else None
               end
             else None
         end = Some (P8D2Record fields, suffix)).
      rewrite p8_f1_frame_count_roundtrip, Guard.
      rewrite (p8_f1_fields_loop_complete_from_children
        fuel IH fields suffix ValidFields ListBound).
      rewrite Strict, ValidFields. reflexivity.
Qed.

Theorem p8_f1_universal_model_roundtrip :
  forall form,
    p8_d2_valid_form form = true ->
    p8_e1_decode_form (p8_e1_put_form form) = Some form.
Proof.
  intros form Valid.
  assert (Enough :
    length (p8_e1_put_form form) <=
    S (length (p8_e1_put_form form))) by lia.
  pose proof (p8_f1_form_prefix_fuel_bound
    (S (length (p8_e1_put_form form))) form [] Valid Enough)
    as Prefix.
  rewrite app_nil_r in Prefix.
  unfold p8_e1_decode_form, p8_e1_parse_form_prefix.
  rewrite Prefix. reflexivity.
Qed.

Theorem p8_f1_universal_model_injective :
  forall left right,
    p8_d2_valid_form left = true ->
    p8_d2_valid_form right = true ->
    p8_e1_put_form left = p8_e1_put_form right ->
    left = right.
Proof.
  intros left right ValidLeft ValidRight Equal.
  pose proof (p8_f1_universal_model_roundtrip left ValidLeft) as L.
  pose proof (p8_f1_universal_model_roundtrip right ValidRight) as R.
  rewrite Equal in L. rewrite R in L. congruence.
Qed.

Theorem p8_f1_universal_model_trailing_rejected :
  forall form trailing,
    p8_d2_valid_form form = true ->
    trailing <> [] ->
    p8_e1_decode_form (p8_e1_put_form form ++ trailing) = None.
Proof.
  intros form trailing Valid Nonempty.
  assert (Enough :
    length (p8_e1_put_form form) <=
    S (length (p8_e1_put_form form ++ trailing))).
  { rewrite app_length. lia. }
  pose proof (p8_f1_form_prefix_fuel_bound
    (S (length (p8_e1_put_form form ++ trailing)))
    form trailing Valid Enough) as Prefix.
  unfold p8_e1_decode_form, p8_e1_parse_form_prefix.
  rewrite Prefix.
  destruct trailing as [|b rest]; [contradiction|reflexivity].
Qed.

Theorem p8_f1_universal_normalized_wire_roundtrip :
  forall form,
    p8_d2_valid_form form = true ->
    p8_e2_normalize_form (p8_e1_put_form form) = Some form.
Proof.
  intros form Valid.
  apply (proj2 (p8_e2_normalized_form_exact_characterization
    (p8_e1_put_form form) form)).
  repeat split; try assumption; try reflexivity.
  apply p8_f1_universal_model_roundtrip. exact Valid.
Qed.

Print Assumptions p8_f1_form_prefix_fuel_bound.
Print Assumptions p8_f1_universal_model_roundtrip.
Print Assumptions p8_f1_universal_model_injective.
Print Assumptions p8_f1_universal_model_trailing_rejected.
Print Assumptions p8_f1_universal_normalized_wire_roundtrip.

Print Assumptions p8_f1_forms_loop_complete_from_children.
Print Assumptions p8_f1_fields_loop_complete_from_children.

Print Assumptions p8_f1_atom_prefix_all_fuel.
Print Assumptions p8_f1_empty_ordered_prefix.
Print Assumptions p8_f1_empty_unordered_prefix.
Print Assumptions p8_f1_empty_record_prefix.
Print Assumptions p8_f1_atom_decode_roundtrip.
Print Assumptions p8_f1_atom_trailing_rejected.
Print Assumptions p8_f1_atom_wire_injective.

Print Assumptions p8_f1_digit_value_append.
Print Assumptions p8_f1_count_scan_suffix.
Print Assumptions p8_f1_read_canonical_digits.
Print Assumptions p8_f1_decimal_fuel_digits.
Print Assumptions p8_f1_decimal_fuel_value.
Print Assumptions p8_f1_decimal_fuel_canonical.
Print Assumptions p8_f1_frame_count_roundtrip.
Print Assumptions p8_f1_text_prefix_roundtrip.
Print Assumptions p8_f1_decoder_is_exact_on_a_success.
Print Assumptions p8_f1_put_form_has_tag.
Print Assumptions p8_f1_put_text_has_tag.
Print Assumptions p8_f1_forms_count_fits_canonical_wire.
Print Assumptions p8_f1_fields_count_fits_canonical_wire.
