From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementPropositionSpine
  GrammarAstGenericRequirementsEffectsSpine.

(*
  Lift the effects-refined generic-requirements carrier into the current
  end-of-chain record_decl and data_decl carriers.

  All already-refined declaration fields remain unchanged; only requirements
  advance from option Phase1SurfaceGenericRequirementsPropositionSpine to
  option Phase1SurfaceGenericRequirementsEffectsSpine.
*)

Record Phase1SurfaceRecordGenericRequirementEffectsSpine : Type := {
  phase1_record_generic_requirement_effects_spine_name : string;
  phase1_record_generic_requirement_effects_spine_generic_params :
    option Phase1SurfaceGenericParamsKindTypeSpine;
  phase1_record_generic_requirement_effects_spine_mode :
    option Phase1SurfaceStructuralMode;
  phase1_record_generic_requirement_effects_spine_requirements :
    option Phase1SurfaceGenericRequirementsEffectsSpine;
  phase1_record_generic_requirement_effects_spine_fields :
    option Phase1SurfaceFieldTypeListSpine
}.

Definition phase1_surface_record_generic_requirement_effects_spine_tree
  (record : Phase1SurfaceRecordGenericRequirementEffectsSpine) : ParseTree :=
  PTNonterminal "record_decl"
    (PTSequence
      [ PTLiteral "record";
        phase1_surface_identifier_tree
          (phase1_record_generic_requirement_effects_spine_name record);
        phase1_surface_optional_generic_params_kind_type_tree
          (phase1_record_generic_requirement_effects_spine_generic_params
            record);
        phase1_surface_optional_mode_tree
          (phase1_record_generic_requirement_effects_spine_mode record);
        phase1_surface_optional_generic_requirements_effects_tree
          (phase1_record_generic_requirement_effects_spine_requirements record);
        PTLiteral "{";
        phase1_surface_optional_field_type_list_tree
          (phase1_record_generic_requirement_effects_spine_fields record);
        PTLiteral "}"
      ]).

Definition
  phase1_surface_normalize_record_generic_requirement_effects_spine
  (record : Phase1SurfaceRecordGenericRequirementPropositionSpine)
  : option Phase1SurfaceRecordGenericRequirementEffectsSpine :=
  match
    phase1_surface_normalize_optional_generic_requirements_effects
      (phase1_record_generic_requirement_proposition_spine_requirements record)
  with
  | Some requirements =>
      Some
        {| phase1_record_generic_requirement_effects_spine_name :=
             phase1_record_generic_requirement_proposition_spine_name record;
           phase1_record_generic_requirement_effects_spine_generic_params :=
             phase1_record_generic_requirement_proposition_spine_generic_params
               record;
           phase1_record_generic_requirement_effects_spine_mode :=
             phase1_record_generic_requirement_proposition_spine_mode record;
           phase1_record_generic_requirement_effects_spine_requirements :=
             requirements;
           phase1_record_generic_requirement_effects_spine_fields :=
             phase1_record_generic_requirement_proposition_spine_fields record |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_record_generic_requirement_effects_spine_round_trip :
  forall record refined,
    phase1_surface_normalize_record_generic_requirement_effects_spine record =
      Some refined ->
    phase1_surface_record_generic_requirement_effects_spine_tree refined =
      phase1_surface_record_generic_requirement_proposition_spine_tree record.
Proof.
  intros [name generic_params mode requirements fields] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_effects requirements)
    as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_generic_requirements_effects_round_trip
      requirements actual Hrequirements).
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_record_generic_requirement_effects_tree
  (tree : ParseTree)
  : option Phase1SurfaceRecordGenericRequirementEffectsSpine :=
  match
    phase1_surface_normalize_record_generic_requirement_proposition_tree tree
  with
  | Some record =>
      phase1_surface_normalize_record_generic_requirement_effects_spine record
  | None => None
  end.

Theorem
  phase1_surface_normalize_record_generic_requirement_effects_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_record_generic_requirement_effects_tree tree =
      Some refined ->
    phase1_surface_record_generic_requirement_effects_spine_tree refined =
      tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_record_generic_requirement_effects_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_record_generic_requirement_proposition_tree tree)
    as [record |] eqn:Hrecord; try discriminate Hnormalize.
  transitivity
    (phase1_surface_record_generic_requirement_proposition_spine_tree record).
  - eapply
      phase1_surface_normalize_record_generic_requirement_effects_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_record_generic_requirement_proposition_tree_round_trip.
    exact Hrecord.
Qed.

Record Phase1SurfaceDataGenericRequirementEffectsSpine : Type := {
  phase1_data_generic_requirement_effects_spine_name : string;
  phase1_data_generic_requirement_effects_spine_generic_params :
    option Phase1SurfaceGenericParamsKindTypeSpine;
  phase1_data_generic_requirement_effects_spine_mode :
    option Phase1SurfaceStructuralMode;
  phase1_data_generic_requirement_effects_spine_requirements :
    option Phase1SurfaceGenericRequirementsEffectsSpine;
  phase1_data_generic_requirement_effects_spine_first_variant :
    Phase1SurfaceRecordFieldTypeVariantSpine;
  phase1_data_generic_requirement_effects_spine_rest_variants :
    list Phase1SurfaceRecordFieldTypeVariantSpine
}.

Definition phase1_surface_data_generic_requirement_effects_spine_tree
  (data_value : Phase1SurfaceDataGenericRequirementEffectsSpine)
  : ParseTree :=
  PTNonterminal "data_decl"
    (PTSequence
      [ PTLiteral "data";
        phase1_surface_identifier_tree
          (phase1_data_generic_requirement_effects_spine_name data_value);
        phase1_surface_optional_generic_params_kind_type_tree
          (phase1_data_generic_requirement_effects_spine_generic_params
            data_value);
        phase1_surface_optional_mode_tree
          (phase1_data_generic_requirement_effects_spine_mode data_value);
        phase1_surface_optional_generic_requirements_effects_tree
          (phase1_data_generic_requirement_effects_spine_requirements
            data_value);
        PTLiteral "=";
        phase1_surface_record_field_type_variant_spine_tree
          (phase1_data_generic_requirement_effects_spine_first_variant
            data_value);
        PTRepetition
          (map phase1_surface_record_field_type_data_suffix_tree
            (phase1_data_generic_requirement_effects_spine_rest_variants
              data_value));
        PTLiteral ";"
      ]).

Definition
  phase1_surface_normalize_data_generic_requirement_effects_spine
  (data_value : Phase1SurfaceDataGenericRequirementPropositionSpine)
  : option Phase1SurfaceDataGenericRequirementEffectsSpine :=
  match
    phase1_surface_normalize_optional_generic_requirements_effects
      (phase1_data_generic_requirement_proposition_spine_requirements data_value)
  with
  | Some requirements =>
      Some
        {| phase1_data_generic_requirement_effects_spine_name :=
             phase1_data_generic_requirement_proposition_spine_name data_value;
           phase1_data_generic_requirement_effects_spine_generic_params :=
             phase1_data_generic_requirement_proposition_spine_generic_params
               data_value;
           phase1_data_generic_requirement_effects_spine_mode :=
             phase1_data_generic_requirement_proposition_spine_mode data_value;
           phase1_data_generic_requirement_effects_spine_requirements :=
             requirements;
           phase1_data_generic_requirement_effects_spine_first_variant :=
             phase1_data_generic_requirement_proposition_spine_first_variant
               data_value;
           phase1_data_generic_requirement_effects_spine_rest_variants :=
             phase1_data_generic_requirement_proposition_spine_rest_variants
               data_value |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_data_generic_requirement_effects_spine_round_trip :
  forall data_value refined,
    phase1_surface_normalize_data_generic_requirement_effects_spine data_value =
      Some refined ->
    phase1_surface_data_generic_requirement_effects_spine_tree refined =
      phase1_surface_data_generic_requirement_proposition_spine_tree data_value.
Proof.
  intros
    [name generic_params mode requirements first_variant rest_variants]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_effects requirements)
    as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_generic_requirements_effects_round_trip
      requirements actual Hrequirements).
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_data_generic_requirement_effects_tree
  (tree : ParseTree)
  : option Phase1SurfaceDataGenericRequirementEffectsSpine :=
  match
    phase1_surface_normalize_data_generic_requirement_proposition_tree tree
  with
  | Some data_value =>
      phase1_surface_normalize_data_generic_requirement_effects_spine data_value
  | None => None
  end.

Theorem
  phase1_surface_normalize_data_generic_requirement_effects_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_data_generic_requirement_effects_tree tree =
      Some refined ->
    phase1_surface_data_generic_requirement_effects_spine_tree refined =
      tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_data_generic_requirement_effects_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_data_generic_requirement_proposition_tree tree)
    as [data_value |] eqn:Hdata; try discriminate Hnormalize.
  transitivity
    (phase1_surface_data_generic_requirement_proposition_spine_tree data_value).
  - eapply
      phase1_surface_normalize_data_generic_requirement_effects_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_data_generic_requirement_proposition_tree_round_trip.
    exact Hdata.
Qed.
