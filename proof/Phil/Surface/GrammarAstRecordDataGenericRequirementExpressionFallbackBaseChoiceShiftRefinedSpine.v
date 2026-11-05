From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceSpine
  GrammarAstGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the completed shift-refined generic-requirements carrier into the
  record_decl and data_decl consumers.

  A single explicit fuel value is threaded through the optional requirements
  field. Every other already-refined declaration field is preserved exactly.

  Structural Rocq surface correspondence only. This slice proves spine/tree
  round trips for the declaration lift; it does not yet prove declaration-level
  derivation-driven fuel totality, change Grammar-v1, Haskell/runtime behavior,
  or evaluation semantics. It continues PHIL-SURFACE-GRAMMAR-CORR-001 after
  #1494.
*)

Record
  Phase1SurfaceRecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine
  : Type := {
  phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_name :
    string;
  phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_generic_params :
    option Phase1SurfaceGenericParamsKindTypeSpine;
  phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_mode :
    option Phase1SurfaceStructuralMode;
  phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_requirements :
    option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine;
  phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fields :
    option Phase1SurfaceFieldTypeListSpine
}.

Definition
  phase1_surface_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
  (record :
    Phase1SurfaceRecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  PTNonterminal "record_decl"
    (PTSequence
      [ PTLiteral "record";
        phase1_surface_identifier_tree
          (phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_name
            record);
        phase1_surface_optional_generic_params_kind_type_tree
          (phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_generic_params
            record);
        phase1_surface_optional_mode_tree
          (phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_mode
            record);
        phase1_surface_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree
          (phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_requirements
            record);
        PTLiteral "{";
        phase1_surface_optional_field_type_list_tree
          (phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fields
            record);
        PTLiteral "}"
      ]).

Definition
  phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
  (fuel : nat)
  (record : Phase1SurfaceRecordGenericRequirementExpressionFallbackBaseChoiceSpine)
  : option
      Phase1SurfaceRecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
      fuel
      (phase1_record_generic_requirement_expression_fallback_base_choice_spine_requirements
        record)
  with
  | Some requirements =>
      Some
        {| phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_name :=
             phase1_record_generic_requirement_expression_fallback_base_choice_spine_name
               record;
           phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_generic_params :=
             phase1_record_generic_requirement_expression_fallback_base_choice_spine_generic_params
               record;
           phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_mode :=
             phase1_record_generic_requirement_expression_fallback_base_choice_spine_mode
               record;
           phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_requirements :=
             requirements;
           phase1_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fields :=
             phase1_record_generic_requirement_expression_fallback_base_choice_spine_fields
               record |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip :
  forall fuel record refined,
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel record = Some refined ->
    phase1_surface_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    phase1_surface_record_generic_requirement_expression_fallback_base_choice_spine_tree
      record.
Proof.
  intros fuel [name generic_params mode requirements fields] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
      fuel requirements)
    as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel_round_trip
      fuel requirements actual Hrequirements).
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option
      Phase1SurfaceRecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree
      tree
  with
  | Some record =>
      phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel record
  | None => None
  end.

Theorem
  phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
      refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree
      tree)
    as [record |] eqn:Hrecord; try discriminate Hnormalize.
  transitivity
    (phase1_surface_record_generic_requirement_expression_fallback_base_choice_spine_tree
      record).
  - eapply
      phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree_round_trip.
    exact Hrecord.
Qed.

Record
  Phase1SurfaceDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine
  : Type := {
  phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_name :
    string;
  phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_generic_params :
    option Phase1SurfaceGenericParamsKindTypeSpine;
  phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_mode :
    option Phase1SurfaceStructuralMode;
  phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_requirements :
    option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceShiftRefinedSpine;
  phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_first_variant :
    Phase1SurfaceRecordFieldTypeVariantSpine;
  phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_rest_variants :
    list Phase1SurfaceRecordFieldTypeVariantSpine
}.

Definition
  phase1_surface_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
  (data_value :
    Phase1SurfaceDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine)
  : ParseTree :=
  PTNonterminal "data_decl"
    (PTSequence
      [ PTLiteral "data";
        phase1_surface_identifier_tree
          (phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_name
            data_value);
        phase1_surface_optional_generic_params_kind_type_tree
          (phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_generic_params
            data_value);
        phase1_surface_optional_mode_tree
          (phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_mode
            data_value);
        phase1_surface_optional_generic_requirements_expression_fallback_base_choice_shift_refined_tree
          (phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_requirements
            data_value);
        PTLiteral "=";
        phase1_surface_record_field_type_variant_spine_tree
          (phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_first_variant
            data_value);
        PTRepetition
          (map phase1_surface_record_field_type_data_suffix_tree
            (phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_rest_variants
              data_value));
        PTLiteral ";"
      ]).

Definition
  phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
  (fuel : nat)
  (data_value :
    Phase1SurfaceDataGenericRequirementExpressionFallbackBaseChoiceSpine)
  : option
      Phase1SurfaceDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
      fuel
      (phase1_data_generic_requirement_expression_fallback_base_choice_spine_requirements
        data_value)
  with
  | Some requirements =>
      Some
        {| phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_name :=
             phase1_data_generic_requirement_expression_fallback_base_choice_spine_name
               data_value;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_generic_params :=
             phase1_data_generic_requirement_expression_fallback_base_choice_spine_generic_params
               data_value;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_mode :=
             phase1_data_generic_requirement_expression_fallback_base_choice_spine_mode
               data_value;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_requirements :=
             requirements;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_first_variant :=
             phase1_data_generic_requirement_expression_fallback_base_choice_spine_first_variant
               data_value;
           phase1_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_rest_variants :=
             phase1_data_generic_requirement_expression_fallback_base_choice_spine_rest_variants
               data_value |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip :
  forall fuel data_value refined,
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
      fuel data_value = Some refined ->
    phase1_surface_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
      refined =
    phase1_surface_data_generic_requirement_expression_fallback_base_choice_spine_tree
      data_value.
Proof.
  intros fuel
    [name generic_params mode requirements first_variant rest_variants]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel
      fuel requirements)
    as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_generic_requirements_expression_fallback_base_choice_shift_refined_fuel_round_trip
      fuel requirements actual Hrequirements).
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
  (fuel : nat)
  (tree : ParseTree)
  : option
      Phase1SurfaceDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine :=
  match
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree
      tree
  with
  | Some data_value =>
      phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel data_value
  | None => None
  end.

Theorem
  phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip :
  forall fuel tree refined,
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined ->
    phase1_surface_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
      refined = tree.
Proof.
  intros fuel tree refined Hnormalize.
  unfold
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree
      tree)
    as [data_value |] eqn:Hdata; try discriminate Hnormalize.
  transitivity
    (phase1_surface_data_generic_requirement_expression_fallback_base_choice_spine_tree
      data_value).
  - eapply
      phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree_round_trip.
    exact Hdata.
Qed.
