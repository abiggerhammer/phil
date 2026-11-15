From Coq Require Import List Bool Arith.PeanoNat Lia.
From Phil.Verification Require Import P8D1UnicodeStreamModel P8D2StructuralOrderModel.
Import ListNotations.

(* P8-E1 diagnostic wire bytes are a pure recursive model, not native
   source admission or Haskell Data.Text/containers operational semantics. *)
Definition p8_e1_digit (b : nat) : bool := (48 <=? b) && (b <=? 57).

(* Canonical decimal digits for a natural count. This encodes only frame
   lengths/arity; no Phil source or application identity is a natural. *)
Fixpoint p8_e1_decimal_fuel (fuel n : nat) : list nat :=
  match fuel with
  | 0 => [48 + n mod 10]
  | S f =>
      if n <? 10 then [48 + n]
      else p8_e1_decimal_fuel f (n / 10) ++ [48 + n mod 10]
  end.
Definition p8_e1_decimal (n : nat) : list nat :=
  p8_e1_decimal_fuel (S n) n.
Definition p8_e1_frame_count (n : nat) : list nat :=
  p8_e1_decimal n ++ [58].

(* Strict scanner: digits, nonempty canonical decimal, colon. *)
Fixpoint p8_e1_count_scan (bs : list nat) (value digits : nat)
    (zero_first : bool) : option (nat * list nat) :=
  match bs with
  | [] => None
  | b :: rest =>
      if b =? 58 then
        if digits =? 0 then None else Some (value, rest)
      else if p8_e1_digit b then
        if zero_first then None
        else p8_e1_count_scan rest (value * 10 + (b - 48)) (S digits)
          ((digits =? 0) && (b =? 48))
      else None
  end.
Definition p8_e1_read_count (bs : list nat) : option (nat * list nat) :=
  p8_e1_count_scan bs 0 0 false.

(* Retain exact consumed-prefix/remainder, reject truncated payloads. *)
Definition p8_e1_take (n : nat) (bs : list nat)
  : option (list nat * list nat) :=
  if n <=? length bs then Some (firstn n bs, skipn n bs) else None.

Definition p8_e1_put_text (utf8 : list nat) : list nat :=
  116 :: p8_e1_frame_count (length utf8) ++ utf8.
Definition p8_e1_parse_text (bs : list nat)
  : option (list nat * list nat) :=
  match bs with
  | [] => None
  | tag :: rest =>
      if tag =? 116 then
        match p8_e1_read_count rest with
        | None => None
        | Some (n, after_count) =>
            match p8_e1_take n after_count with
            | None => None
            | Some (txt, suffix) =>
                if p8_d2_text_valid txt then Some (txt, suffix) else None
            end
        end
      else None
  end.

Fixpoint p8_e1_forms_count (xs : P8D2Forms) : nat :=
  match xs with
  | P8D2Nil => 0
  | P8D2Cons _ rest => S (p8_e1_forms_count rest)
  end.
Fixpoint p8_e1_fields_count (xs : P8D2Fields) : nat :=
  match xs with
  | P8D2FieldNil => 0
  | P8D2FieldCons _ _ rest => S (p8_e1_fields_count rest)
  end.

(* Actual a/o/u/r tags; member ordering follows the D2 recursive native
   constructor order, NOT the lexicographic tag-byte order u > r. *)
Fixpoint p8_e1_put_form (f : P8D2Form) : list nat :=
  match f with
  | P8D2Atom utf8 => 97 :: p8_e1_put_text utf8
  | P8D2Ordered xs =>
      111 :: p8_e1_frame_count (p8_e1_forms_count xs) ++ p8_e1_put_forms xs
  | P8D2Unordered xs =>
      117 :: p8_e1_frame_count (p8_e1_forms_count xs) ++ p8_e1_put_forms xs
  | P8D2Record xs =>
      114 :: p8_e1_frame_count (p8_e1_fields_count xs) ++ p8_e1_put_fields xs
  end
with p8_e1_put_forms (xs : P8D2Forms) : list nat :=
  match xs with
  | P8D2Nil => []
  | P8D2Cons f rest => p8_e1_put_form f ++ p8_e1_put_forms rest
  end
with p8_e1_put_fields (xs : P8D2Fields) : list nat :=
  match xs with
  | P8D2FieldNil => []
  | P8D2FieldCons key value rest =>
      p8_e1_put_text key ++ p8_e1_put_form value ++ p8_e1_put_fields rest
  end.

(* Finite input-length fuel bounds depth because every successful nested
   form consumes its own tag octet. Local child/field recursors count down
   the actual canonical declared cardinality, capped by remaining bytes. *)
Fixpoint p8_e1_parse_form_fuel (fuel : nat) (bs : list nat)
  {struct fuel} : option (P8D2Form * list nat) :=
  match fuel with
  | 0 => None
  | S smaller =>
      let fix parse_forms (n : nat) (wire : list nat) {struct n}
          : option (P8D2Forms * list nat) :=
        match n with
        | 0 => Some (P8D2Nil, wire)
        | S remaining =>
            match p8_e1_parse_form_fuel smaller wire with
            | None => None
            | Some (child, next) =>
                match parse_forms remaining next with
                | None => None
                | Some (children, suffix) =>
                    Some (P8D2Cons child children, suffix)
                end
            end
        end in
      let fix parse_fields (n : nat) (wire : list nat) {struct n}
          : option (P8D2Fields * list nat) :=
        match n with
        | 0 => Some (P8D2FieldNil, wire)
        | S remaining =>
            match p8_e1_parse_text wire with
            | None => None
            | Some (key, after_key) =>
                match p8_e1_parse_form_fuel smaller after_key with
                | None => None
                | Some (value, after_value) =>
                    match parse_fields remaining after_value with
                    | None => None
                    | Some (fields, suffix) =>
                        Some (P8D2FieldCons key value fields, suffix)
                    end
                end
            end
        end in
      match bs with
      | [] => None
      | tag :: rest =>
          if tag =? 97 then
            match p8_e1_parse_text rest with
            | None => None
            | Some (txt, suffix) => Some (P8D2Atom txt, suffix)
            end
          else
            match p8_e1_read_count rest with
            | None => None
            | Some (n, after_count) =>
                if n <=? length after_count then
                  if tag =? 111 then
                    match parse_forms n after_count with
                    | Some (xs, suffix) => Some (P8D2Ordered xs, suffix)
                    | None => None
                    end
                  else if tag =? 117 then
                    match parse_forms n after_count with
                    | Some (xs, suffix) =>
                        if p8_d2_strict_members xs
                           && p8_d2_valid_forms xs
                        then Some (P8D2Unordered xs, suffix) else None
                    | None => None
                    end
                  else if tag =? 114 then
                    match parse_fields n after_count with
                    | Some (xs, suffix) =>
                        if p8_d2_strict_keys xs
                           && p8_d2_valid_fields xs
                        then Some (P8D2Record xs, suffix) else None
                    | None => None
                    end
                  else None
                else None
            end
      end
  end.
Definition p8_e1_parse_form_prefix (bs : list nat)
  : option (P8D2Form * list nat) :=
  p8_e1_parse_form_fuel (S (length bs)) bs.
Definition p8_e1_decode_form (bs : list nat) : option P8D2Form :=
  match p8_e1_parse_form_prefix bs with
  | Some (form, []) => Some form
  | _ => None
  end.

(* Substantive universally quantified parser/framing conservation. *)
Lemma p8_e1_take_exact_sound :
  forall n bytes fragment suffix,
    p8_e1_take n bytes = Some (fragment, suffix) ->
    length fragment = n /\ bytes = fragment ++ suffix.
Proof.
  intros n bytes fragment suffix H.
  unfold p8_e1_take in H.
  destruct (n <=? length bytes) eqn:E; try discriminate.
  inversion H; subst; clear H.
  apply Nat.leb_le in E.
  split.
  - rewrite firstn_length, Nat.min_l by lia. reflexivity.
  - symmetry. apply firstn_skipn.
Qed.

Theorem p8_e1_take_exact_prefix :
  forall fragment suffix,
    p8_e1_take (length fragment) (fragment ++ suffix) =
      Some (fragment, suffix).
Proof.
  intros fragment suffix.
  unfold p8_e1_take.
  rewrite app_length.
  assert (length fragment <=? length fragment + length suffix = true)
    as E by (apply Nat.leb_le; lia).
  rewrite E.
  rewrite firstn_app, skipn_app.
  rewrite firstn_all, skipn_all, Nat.sub_diag.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Theorem p8_e1_parse_text_prefix_conservation :
  forall wire txt suffix,
    p8_e1_parse_text wire = Some (txt, suffix) ->
    p8_d2_text_valid txt = true /\
    exists after_tag n after_count,
      wire = 116 :: after_tag /\
      p8_e1_read_count after_tag = Some (n, after_count) /\
      length txt = n /\
      after_count = txt ++ suffix.
Proof.
  intros [|tag after_tag] txt suffix H; try discriminate.
  unfold p8_e1_parse_text in H. simpl in H.
  destruct (tag =? 116) eqn:Tag; try discriminate.
  apply Nat.eqb_eq in Tag. subst tag.
  destruct (p8_e1_read_count after_tag) as [[n after_count]|] eqn:C;
    try discriminate.
  destruct (p8_e1_take n after_count) as [[fragment trailing]|] eqn:T;
    try discriminate.
  destruct (p8_d2_text_valid fragment) eqn:V; try discriminate.
  inversion H; subst; clear H.
  apply p8_e1_take_exact_sound in T as [Len Split].
  split; [exact V|].
  exists after_tag, n, after_count.
  repeat split; try reflexivity; assumption.
Qed.

Theorem p8_e1_parsed_text_is_strict_unicode :
  forall wire txt suffix,
    p8_e1_parse_text wire = Some (txt, suffix) ->
    exists scalars,
      p8_d1_decode txt = Some scalars /\
      p8_d1_valid scalars = true /\
      p8_d1_encode scalars = txt.
Proof.
  intros wire txt suffix H.
  apply p8_e1_parse_text_prefix_conservation in H as [Valid _].
  unfold p8_d2_text_valid in Valid.
  destruct (p8_d1_decode txt) as [scalars|] eqn:E; try discriminate.
  exists scalars. split; [exact E|].
  apply p8_d1_stream_canonical_acceptance in E as [Wellformed Enc].
  split; assumption.
Qed.

(* Executable concrete boundary and tamper witnesses. E2 must prove the
   missing general recursive count inversion and structural roundtrip. *)
Example p8_e1_decimal_zero : p8_e1_frame_count 0 = [48;58].
Proof. reflexivity. Qed.
Example p8_e1_decimal_hundred : p8_e1_frame_count 100 = [49;48;48;58].
Proof. reflexivity. Qed.
Example p8_e1_nul_unicode_atom :
  p8_e1_decode_form [97;116;55;58;0;195;169;240;159;153;130] =
    Some (P8D2Atom [0;195;169;240;159;153;130]).
Proof. reflexivity. Qed.
Example p8_e1_unicode_atom :
  p8_e1_decode_form [97;116;54;58;195;169;240;159;153;130] =
    Some (P8D2Atom [195;169;240;159;153;130]).
Proof. reflexivity. Qed.
Example p8_e1_nul_atom :
  p8_e1_decode_form [97;116;51;58;0;97;0] =
    Some (P8D2Atom [0;97;0]).
Proof. reflexivity. Qed.
Example p8_e1_nested_ordered :
  p8_e1_decode_form [111;50;58;97;116;49;58;97;97;116;49;58;98] =
    Some (P8D2Ordered (P8D2Cons (P8D2Atom [97])
      (P8D2Cons (P8D2Atom [98]) P8D2Nil))).
Proof. reflexivity. Qed.
Example p8_e1_reject_leading_zero_count :
  p8_e1_decode_form [111;48;49;58;97;116;48;58] = None.
Proof. reflexivity. Qed.
Example p8_e1_reject_truncated_nested :
  p8_e1_decode_form [111;50;58;97;116;49;58;97] = None.
Proof. reflexivity. Qed.
Example p8_e1_reject_duplicate_set :
  p8_e1_decode_form [117;50;58;97;116;49;58;97;97;116;49;58;97] = None.
Proof. reflexivity. Qed.
Example p8_e1_reject_duplicate_record :
  p8_e1_decode_form
    [114;50;58;116;49;58;97;97;116;48;58;
     116;49;58;97;97;116;48;58] = None.
Proof. reflexivity. Qed.
Example p8_e1_reject_invalid_utf8 :
  p8_e1_decode_form [97;116;50;58;192;128] = None.
Proof. reflexivity. Qed.
Example p8_e1_reject_trailing :
  p8_e1_decode_form [97;116;49;58;97;0] = None.
Proof. reflexivity. Qed.

Print Assumptions p8_e1_take_exact_sound.
Print Assumptions p8_e1_take_exact_prefix.
Print Assumptions p8_e1_parse_text_prefix_conservation.
Print Assumptions p8_e1_parsed_text_is_strict_unicode.
