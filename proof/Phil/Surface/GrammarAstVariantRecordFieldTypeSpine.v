From Phil.Surface Require Import
  GrammarAstVariantPayloadSpine
  GrammarAstOptionalFieldTypeSpine.

(*
  Refine only the record-shaped variant payload field list.

  Tuple-shaped variant payloads are already independent of record fields and
  are preserved unchanged here.
*)

Inductive Phase1SurfaceRecordFieldTypeVariantPayloadSpine : Type :=
| Phase1RecordFieldTypeVariantRecordPayloadSpine
    (fields : option Phase1SurfaceFieldTypeListSpine)
| Phase1RecordFieldTypeVariantTuplePayloadSpine
    (types : option Phase1SurfaceTupleTypeListSpine).

Definition phase1_surface_record_field_type_variant_payload_spine_index
  (payload : Phase1SurfaceRecordFieldTypeVariantPayloadSpine) : nat :=
  match payload with
  | Phase1RecordFieldTypeVariantRecordPayloadSpine _ => 0
  | Phase1RecordFieldTypeVariantTuplePayloadSpine _ => 1
  end.

Definition phase1_surface_record_field_type_variant_payload_selected_tree
  (payload : Phase1SurfaceRecordFieldTypeVariantPayloadSpine) : ParseTree :=
  match payload with
  | Phase1RecordFieldTypeVariantRecordPayloadSpine fields =>
      PTSequence
        [ PTLiteral "{";
          phase1_surface_optional_field_type_list_tree fields;
          PTLiteral "}"
        ]
  | Phase1RecordFieldTypeVariantTuplePayloadSpine types =>
      PTSequence
        [ PTLiteral "(";
          phase1_surface_optional_tuple_types_tree types;
          PTLiteral ")"
        ]
  end.

Definition phase1_surface_record_field_type_variant_payload_spine_tree
  (payload : Phase1SurfaceRecordFieldTypeVariantPayloadSpine) : ParseTree :=
  PTNonterminal "variant_payload"
    (PTAlternative
      (phase1_surface_record_field_type_variant_payload_spine_index payload)
      (phase1_surface_record_field_type_variant_payload_selected_tree payload)).

Definition phase1_surface_normalize_record_field_type_variant_payload_spine
  (payload : Phase1SurfaceVariantPayloadSpine)
  : option Phase1SurfaceRecordFieldTypeVariantPayloadSpine :=
  match payload with
  | Phase1VariantRecordPayloadSpine fields =>
      match phase1_surface_normalize_optional_field_type_list fields with
      | Some refined =>
          Some (Phase1RecordFieldTypeVariantRecordPayloadSpine refined)
      | None => None
      end
  | Phase1VariantTuplePayloadSpine types =>
      Some (Phase1RecordFieldTypeVariantTuplePayloadSpine types)
  end.

Theorem
  phase1_surface_normalize_record_field_type_variant_payload_spine_round_trip :
  forall payload refined,
    phase1_surface_normalize_record_field_type_variant_payload_spine payload =
      Some refined ->
    phase1_surface_record_field_type_variant_payload_spine_tree refined =
      phase1_surface_variant_payload_spine_tree payload.
Proof.
  intros [fields | types] refined Hnormalize.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_optional_field_type_list fields)
      as [actual |] eqn:Hfields; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_optional_field_type_list_round_trip
        fields actual Hfields).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_record_field_type_variant_payload_tree
  (tree : ParseTree)
  : option Phase1SurfaceRecordFieldTypeVariantPayloadSpine :=
  match phase1_surface_normalize_variant_payload_spine tree with
  | Some payload =>
      phase1_surface_normalize_record_field_type_variant_payload_spine payload
  | None => None
  end.

Theorem
  phase1_surface_normalize_record_field_type_variant_payload_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_record_field_type_variant_payload_tree tree =
      Some refined ->
    phase1_surface_record_field_type_variant_payload_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_record_field_type_variant_payload_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_variant_payload_spine tree)
    as [payload |] eqn:Hpayload; try discriminate Hnormalize.
  transitivity (phase1_surface_variant_payload_spine_tree payload).
  - eapply
      phase1_surface_normalize_record_field_type_variant_payload_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_variant_payload_spine_round_trip.
    exact Hpayload.
Qed.
