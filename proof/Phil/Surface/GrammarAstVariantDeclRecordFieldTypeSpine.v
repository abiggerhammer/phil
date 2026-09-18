From Phil.Surface Require Import
  GrammarAstVariantPayloadSpine
  GrammarAstVariantRecordFieldTypeSpine.

(*
  Lift the record-field-type-refined variant payload through the optional
  payload wrapper and into variant_decl.

  Variant names are already normalized by the predecessor carrier and are
  preserved unchanged.
*)

Definition phase1_surface_optional_record_field_type_variant_payload_tree
  (payload : option Phase1SurfaceRecordFieldTypeVariantPayloadSpine)
  : ParseTree :=
  match payload with
  | None => PTOptionalNone
  | Some value =>
      PTOptionalSome
        (phase1_surface_record_field_type_variant_payload_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_record_field_type_variant_payload
  (payload : option Phase1SurfaceVariantPayloadSpine)
  : option (option Phase1SurfaceRecordFieldTypeVariantPayloadSpine) :=
  match payload with
  | None => Some None
  | Some value =>
      match
        phase1_surface_normalize_record_field_type_variant_payload_spine value
      with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_record_field_type_variant_payload_round_trip :
  forall payload refined,
    phase1_surface_normalize_optional_record_field_type_variant_payload payload =
      Some refined ->
    phase1_surface_optional_record_field_type_variant_payload_tree refined =
      phase1_surface_optional_variant_payload_spine_tree payload.
Proof.
  intros [payload |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_record_field_type_variant_payload_spine payload)
      as [actual |] eqn:Hpayload; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_record_field_type_variant_payload_spine_round_trip
        payload actual Hpayload).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Record Phase1SurfaceRecordFieldTypeVariantSpine : Type := {
  phase1_record_field_type_variant_spine_name : string;
  phase1_record_field_type_variant_spine_payload :
    option Phase1SurfaceRecordFieldTypeVariantPayloadSpine
}.

Definition phase1_surface_record_field_type_variant_spine_tree
  (variant : Phase1SurfaceRecordFieldTypeVariantSpine) : ParseTree :=
  PTNonterminal "variant_decl"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_record_field_type_variant_spine_name variant);
        phase1_surface_optional_record_field_type_variant_payload_tree
          (phase1_record_field_type_variant_spine_payload variant)
      ]).

Definition phase1_surface_normalize_record_field_type_variant_spine
  (variant : Phase1SurfaceVariantPayloadVariantSpine)
  : option Phase1SurfaceRecordFieldTypeVariantSpine :=
  match
    phase1_surface_normalize_optional_record_field_type_variant_payload
      (phase1_variant_payload_variant_spine_payload variant)
  with
  | Some payload =>
      Some
        {| phase1_record_field_type_variant_spine_name :=
             phase1_variant_payload_variant_spine_name variant;
           phase1_record_field_type_variant_spine_payload := payload |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_record_field_type_variant_spine_round_trip :
  forall variant refined,
    phase1_surface_normalize_record_field_type_variant_spine variant =
      Some refined ->
    phase1_surface_record_field_type_variant_spine_tree refined =
      phase1_surface_variant_payload_variant_spine_tree variant.
Proof.
  intros [name payload] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_record_field_type_variant_payload payload)
    as [actual |] eqn:Hpayload; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_record_field_type_variant_payload_round_trip
      payload actual Hpayload).
  reflexivity.
Qed.
