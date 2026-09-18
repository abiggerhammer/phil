From Phil.Surface Require Import
  GrammarAstRecordFieldsSpine
  GrammarAstOptionalFieldTypeSpine.

(*
  Lift the refined optional field-list type payload into record_decl.

  The record name, generic parameters, structural mode, and generic
  requirements are already refined by the predecessor carrier and are
  preserved unchanged here.
*)

Record Phase1SurfaceRecordFieldTypeSpine : Type := {
  phase1_record_field_type_spine_name : string;
  phase1_record_field_type_spine_generic_params :
    option Phase1SurfaceGenericParamsSpine;
  phase1_record_field_type_spine_mode : option Phase1SurfaceStructuralMode;
  phase1_record_field_type_spine_requirements :
    option Phase1SurfaceGenericRequirementsSpine;
  phase1_record_field_type_spine_fields :
    option Phase1SurfaceFieldTypeListSpine
}.

Definition phase1_surface_record_field_type_spine_tree
  (record : Phase1SurfaceRecordFieldTypeSpine) : ParseTree :=
  PTNonterminal "record_decl"
    (PTSequence
      [ PTLiteral "record";
        phase1_surface_identifier_tree
          (phase1_record_field_type_spine_name record);
        phase1_surface_optional_generic_params_tree
          (phase1_record_field_type_spine_generic_params record);
        phase1_surface_optional_mode_tree
          (phase1_record_field_type_spine_mode record);
        phase1_surface_optional_generic_requirements_tree
          (phase1_record_field_type_spine_requirements record);
        PTLiteral "{";
        phase1_surface_optional_field_type_list_tree
          (phase1_record_field_type_spine_fields record);
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_record_field_type_spine
  (record : Phase1SurfaceRecordFieldsSpine)
  : option Phase1SurfaceRecordFieldTypeSpine :=
  match
    phase1_surface_normalize_optional_field_type_list
      (phase1_record_fields_spine_fields record)
  with
  | Some fields =>
      Some
        {| phase1_record_field_type_spine_name :=
             phase1_record_fields_spine_name record;
           phase1_record_field_type_spine_generic_params :=
             phase1_record_fields_spine_generic_params record;
           phase1_record_field_type_spine_mode :=
             phase1_record_fields_spine_mode record;
           phase1_record_field_type_spine_requirements :=
             phase1_record_fields_spine_requirements record;
           phase1_record_field_type_spine_fields := fields |}
  | None => None
  end.

Theorem phase1_surface_normalize_record_field_type_spine_round_trip :
  forall record refined,
    phase1_surface_normalize_record_field_type_spine record = Some refined ->
    phase1_surface_record_field_type_spine_tree refined =
      phase1_surface_record_fields_spine_tree record.
Proof.
  intros [name generic_params mode requirements fields]
    refined Hnormalize.
  unfold phase1_surface_normalize_record_field_type_spine in Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_optional_field_type_list fields)
    as [actual |] eqn:Hfields; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_field_type_list_round_trip
      fields actual Hfields).
  reflexivity.
Qed.

Definition phase1_surface_normalize_record_field_type_tree
  (tree : ParseTree) : option Phase1SurfaceRecordFieldTypeSpine :=
  match phase1_surface_normalize_record_fields_tree tree with
  | Some record => phase1_surface_normalize_record_field_type_spine record
  | None => None
  end.

Theorem phase1_surface_normalize_record_field_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_record_field_type_tree tree = Some refined ->
    phase1_surface_record_field_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_record_field_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_record_fields_tree tree)
    as [record |] eqn:Hrecord; try discriminate Hnormalize.
  transitivity (phase1_surface_record_fields_spine_tree record).
  - eapply phase1_surface_normalize_record_field_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_record_fields_tree_round_trip.
    exact Hrecord.
Qed.
