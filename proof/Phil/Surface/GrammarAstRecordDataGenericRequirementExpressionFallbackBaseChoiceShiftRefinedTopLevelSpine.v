From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclarationFuelSupport.

(*
  Lift the shift-refined record/data declaration carrier through the existing
  top_level_decl attribute/declaration spine.

  Attributes remain represented by the already-proved Phase1SurfaceAttributeSpine
  list.  Only record_decl/data_decl declaration payloads are refined here, under
  one explicit fuel value.  Successful refinement reconstructs the exact
  original top-level ParseTree and is stable under larger fuel.

  Structural Rocq surface correspondence only.  This does not add support for
  other declaration families, aggregate top-level lists, lift whole-source
  carriers, change Grammar-v1, or alter runtime/extraction/evaluation behavior.
  Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1504.
*)

Record
  Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelSpine
  : Type := {
  phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_attributes :
    list Phase1SurfaceAttributeSpine;
  phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_declaration :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
}.

Definition
  phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_to_spine
  (declaration :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration)
  : Phase1SurfaceDeclarationSpine :=
  match declaration with
  | Phase1RecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
      record =>
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree :=
           phase1_surface_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
             record |}
  | Phase1DataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
      data_value =>
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree :=
           phase1_surface_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
             data_value |}
  end.

Definition
  phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_tree
  (top_level :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelSpine)
  : ParseTree :=
  phase1_surface_top_level_spine_tree
    {| phase1_top_level_spine_attributes :=
         phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_attributes
           top_level;
       phase1_top_level_spine_declaration :=
         phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_to_spine
           (phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_declaration
             top_level) |}.

Definition
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel
  (fuel : nat)
  (top_level : Phase1SurfaceTopLevelSpine)
  : option
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelSpine :=
  match
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      fuel (phase1_top_level_spine_declaration top_level)
  with
  | Some declaration =>
      Some
        {| phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_attributes :=
             phase1_top_level_spine_attributes top_level;
           phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_declaration :=
             declaration |}
  | None => None
  end.

Lemma
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_full_round_trip :
  forall fuel declaration refined,
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      fuel declaration = Some refined ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_to_spine
      refined =
    declaration.
Proof.
  intros fuel [tag selected_tree] refined Hnormalize.
  destruct tag; cbn in Hnormalize; try discriminate Hnormalize.
  - destruct
      (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel selected_tree)
      as [record |] eqn:Hrecord; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    unfold
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_to_spine.
    cbn.
    rewrite
      (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip
        fuel selected_tree record Hrecord).
    reflexivity.
  - destruct
      (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel selected_tree)
      as [data_value |] eqn:Hdata; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    unfold
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_to_spine.
    cbn.
    rewrite
      (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip
        fuel selected_tree data_value Hdata).
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel_round_trip :
  forall fuel top_level refined,
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel
      fuel top_level = Some refined ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_tree
      refined =
    phase1_surface_top_level_spine_tree top_level.
Proof.
  intros fuel [attributes declaration] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      fuel declaration)
    as [refined_declaration |] eqn:Hdeclaration;
    try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_tree.
  cbn.
  rewrite
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_full_round_trip
      fuel declaration refined_declaration Hdeclaration).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel_monotone :
  forall fuel larger top_level refined,
    fuel <= larger ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel
      fuel top_level = Some refined ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel
      larger top_level = Some refined.
Proof.
  intros fuel larger [attributes declaration] refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      fuel declaration)
    as [refined_declaration |] eqn:Hdeclaration;
    try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_monotone
      fuel larger declaration refined_declaration Hle Hdeclaration).
  reflexivity.
Qed.
