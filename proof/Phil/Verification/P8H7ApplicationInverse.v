From Coq Require Import List Bool Arith.PeanoNat Lia.
From Phil.Verification Require Import
  P8D1UnicodeStreamModel P8D2StructuralOrderModel
  P8E1CanonicalWireModel P8E2CanonicalApplicationModel
  P8F1RecursiveInverseModel.
Import ListNotations.

(*
  P8-H7: pure-model, typed D/V/Q/M GenericApplication inversion.
  New lemmas compose F1's proven recursive-form prefix inverse with the
  exact immutable E2 application parser. These are universal mathematical
  model results only, NOT a native Haskell Text/containers/Builder simulation,
  P2/P6/P7 admission, a TCB addition, or final P10 certification.
*)

Lemma p8_h7_argument_payload_length_bound :
  forall key value,
    length (p8_e1_put_form value) <=
    length (p8_e2_put_argument key value).
Proof.
  intros key value.
  unfold p8_e2_put_argument.
  repeat rewrite length_app. simpl. lia.
Qed.

(* Concrete Q/M framing associativity, independent of any parser tactic. *)
Lemma p8_h7_qm_concat :
  forall (prefix value suffix : list nat),
    prefix ++ (77 :: (value ++ suffix)) =
    (prefix ++ (77 :: value)) ++ suffix.
Proof.
  intros prefix value suffix.
  induction prefix as [|byte rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma p8_h7_argument_prefix :
  forall fuel key value suffix,
    p8_d2_text_valid key = true ->
    p8_d2_valid_form value = true ->
    length (p8_e1_put_form value) <= fuel ->
    p8_e2_parse_argument fuel
      (p8_e2_put_argument key value ++ suffix) =
      Some ((key, value), suffix).
Proof.
  intros fuel key value suffix KeyValid ValueValid Bound.
  unfold p8_e2_put_argument.
  replace (([81] ++ p8_e1_put_text key ++ [77] ++
            p8_e1_put_form value) ++ suffix)
    with (81 :: (p8_e1_put_text key ++
          (77 :: (p8_e1_put_form value ++ suffix)))).
  2: {
    cbn [app].
    f_equal.
    apply p8_h7_qm_concat.
  }
  unfold p8_e2_parse_argument.
  cbn [p8_e2_expect].
  rewrite (p8_f1_text_prefix_roundtrip key
    (77 :: (p8_e1_put_form value ++ suffix)) KeyValid).
  cbn [p8_e2_expect].
  rewrite (p8_f1_form_prefix_fuel_bound fuel value suffix
    ValueValid Bound).
  reflexivity.
Qed.

Lemma p8_h7_arguments_prefix :
  forall fields fuel suffix,
    p8_d2_valid_fields fields = true ->
    length (p8_e2_put_arguments fields) <= fuel ->
    p8_e2_parse_arguments fuel (p8_e1_fields_count fields)
      (p8_e2_put_arguments fields ++ suffix) =
      Some (fields, suffix).
Proof.
  induction fields as [|key value rest IH];
    intros fuel suffix Valid Bound.
  - reflexivity.
  - cbn [p8_d2_valid_fields] in Valid.
    apply andb_true_iff in Valid as [Both RestValid].
    apply andb_true_iff in Both as [KeyValid ValueValid].
    pose proof (p8_h7_argument_payload_length_bound key value)
      as ValueSize.
    cbn [p8_e2_put_arguments] in Bound.
    rewrite length_app in Bound.
    assert (ValueBound : length (p8_e1_put_form value) <= fuel)
      by lia.
    assert (RestBound : length (p8_e2_put_arguments rest) <= fuel)
      by lia.
    cbn [p8_e1_fields_count p8_e2_put_arguments].
    rewrite <- app_assoc.
    cbn [p8_e2_parse_arguments].
    rewrite (p8_h7_argument_prefix fuel key value
      (p8_e2_put_arguments rest ++ suffix)
      KeyValid ValueValid ValueBound).
    rewrite (IH fuel suffix RestValid RestBound).
    reflexivity.
Qed.

Lemma p8_h7_arguments_count_fits_wire :
  forall fields,
    p8_e1_fields_count fields <=
    length (p8_e2_put_arguments fields).
Proof.
  induction fields as [|key value rest IH].
  - reflexivity.
  - cbn [p8_e1_fields_count p8_e2_put_arguments].
    rewrite length_app.
    unfold p8_e2_put_argument.
    repeat rewrite length_app.
    simpl. lia.
Qed.

Lemma p8_h7_application_arguments_fuel :
  forall app suffix,
    length (p8_e2_put_arguments (p8_d2_arguments app)) <=
    S (length (p8_e2_put_application app ++ suffix)).
Proof.
  intros [declaration interface fields] suffix.
  unfold p8_e2_put_application.
  cbn [p8_d2_declaration p8_d2_interface p8_d2_arguments].
  repeat rewrite length_app.
  simpl. lia.
Qed.

Theorem p8_h7_application_raw_prefix :
  forall app suffix,
    p8_d2_valid_application app = true ->
    p8_e2_parse_application_raw
      (p8_e2_put_application app ++ suffix) =
      Some (app, suffix).
Proof.
  intros [declaration interface fields] suffix Valid.
  cbn [p8_d2_valid_application] in Valid.
  apply andb_true_iff in Valid as [First ValidFields].
  apply andb_true_iff in First as [Earlier StrictKeys].
  apply andb_true_iff in Earlier as [ValidDeclaration ValidInterface].
  assert (CountGuard :
    (p8_e1_fields_count fields <=?
     length (p8_e2_put_arguments fields ++ suffix)) = true).
  { apply Nat.leb_le.
    rewrite length_app.
    pose proof (p8_h7_arguments_count_fits_wire fields).
    lia. }
  assert (Enough :
    length (p8_e2_put_arguments fields) <=
    S (length
      (p8_e2_put_application
        {| p8_d2_declaration := declaration;
           p8_d2_interface := interface;
           p8_d2_arguments := fields |} ++ suffix))).
  { apply p8_h7_application_arguments_fuel. }
  replace
    (p8_e2_put_application
      {| p8_d2_declaration := declaration;
         p8_d2_interface := interface;
         p8_d2_arguments := fields |} ++ suffix)
    with
    (103 :: 68 ::
      (p8_e1_put_text declaration ++
        (86 :: (p8_e1_put_text interface ++
          (p8_e1_frame_count (p8_e1_fields_count fields) ++
            (p8_e2_put_arguments fields ++ suffix)))))).
  2: {
    unfold p8_e2_put_application.
    cbn [p8_d2_declaration p8_d2_interface p8_d2_arguments app].
    repeat rewrite <- app_assoc.
    reflexivity.
  }
  unfold p8_e2_parse_application_raw.
  cbn [p8_e2_expect].
  rewrite (p8_f1_text_prefix_roundtrip declaration
    (86 :: (p8_e1_put_text interface ++
      (p8_e1_frame_count (p8_e1_fields_count fields) ++
        (p8_e2_put_arguments fields ++ suffix))))
    ValidDeclaration).
  cbn [p8_e2_expect].
  rewrite (p8_f1_text_prefix_roundtrip interface
    (p8_e1_frame_count (p8_e1_fields_count fields) ++
      (p8_e2_put_arguments fields ++ suffix))
    ValidInterface).
  rewrite (p8_f1_frame_count_roundtrip
    (p8_e1_fields_count fields)
    (p8_e2_put_arguments fields ++ suffix)).
  rewrite CountGuard.
  rewrite (p8_h7_arguments_prefix fields
    (S (length
      (103 :: 68 ::
        (p8_e1_put_text declaration ++
          (86 :: (p8_e1_put_text interface ++
            (p8_e1_frame_count (p8_e1_fields_count fields) ++
              (p8_e2_put_arguments fields ++ suffix))))))))
    suffix ValidFields).
  2: {
    unfold p8_e2_put_application in Enough.
    cbn [p8_d2_declaration p8_d2_interface p8_d2_arguments] in Enough.
    exact Enough.
  }
  reflexivity.
Qed.

Theorem p8_h7_application_prefix :
  forall app suffix,
    p8_d2_valid_application app = true ->
    p8_e2_parse_application_prefix
      (p8_e2_put_application app ++ suffix) =
      Some (app, suffix).
Proof.
  intros app suffix Valid.
  unfold p8_e2_parse_application_prefix.
  rewrite (p8_h7_application_raw_prefix app suffix Valid).
  rewrite Valid. reflexivity.
Qed.

Theorem p8_h7_universal_model_application_inverse :
  forall app,
    p8_d2_valid_application app = true ->
    p8_e2_decode_application (p8_e2_put_application app) = Some app.
Proof.
  intros app Valid.
  unfold p8_e2_decode_application.
  pose proof (p8_h7_application_prefix app [] Valid) as Prefix.
  rewrite app_nil_r in Prefix.
  rewrite Prefix.
  rewrite p8_e2_bytes_equal_refl.
  reflexivity.
Qed.

Theorem p8_h7_universal_model_application_injective :
  forall left right,
    p8_d2_valid_application left = true ->
    p8_d2_valid_application right = true ->
    p8_e2_put_application left = p8_e2_put_application right ->
    left = right.
Proof.
  intros left right ValidLeft ValidRight SameWire.
  pose proof (p8_h7_universal_model_application_inverse left ValidLeft)
    as LeftInverse.
  pose proof (p8_h7_universal_model_application_inverse right ValidRight)
    as RightInverse.
  rewrite SameWire in LeftInverse.
  rewrite RightInverse in LeftInverse.
  congruence.
Qed.

Theorem p8_h7_universal_model_application_trailing_rejected :
  forall app suffix,
    p8_d2_valid_application app = true ->
    suffix <> [] ->
    p8_e2_decode_application (p8_e2_put_application app ++ suffix) = None.
Proof.
  intros app suffix Valid Nonempty.
  unfold p8_e2_decode_application.
  rewrite (p8_h7_application_prefix app suffix Valid).
  destruct suffix as [|x xs]; [contradiction|reflexivity].
Qed.

Print Assumptions p8_h7_argument_prefix.
Print Assumptions p8_h7_arguments_prefix.
Print Assumptions p8_h7_application_raw_prefix.
Print Assumptions p8_h7_application_prefix.
Print Assumptions p8_h7_universal_model_application_inverse.
Print Assumptions p8_h7_universal_model_application_injective.
Print Assumptions p8_h7_universal_model_application_trailing_rejected.
