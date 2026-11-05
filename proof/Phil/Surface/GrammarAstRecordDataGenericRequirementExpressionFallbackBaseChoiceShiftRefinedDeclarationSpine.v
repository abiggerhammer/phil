From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Bridge the completed shift-refined record_decl/data_decl carriers to the
  existing top-level declaration spine.

  One explicit fuel value is threaded through the selected record/data tree.
  Other declaration tags remain outside this focused bridge.

  Structural Rocq surface correspondence only. No Grammar-v1, runtime,
  extraction, or evaluation behavior changes. Continues
  PHIL-SURFACE-GRAMMAR-CORR-001 after #1498.
*)

Inductive
  Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
  : Type :=
| Phase1RecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
    (record :
      Phase1SurfaceRecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine)
| Phase1DataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
    (data_value :
      Phase1SurfaceDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine).

Definition
  phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_tree
  (declaration :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration)
  : ParseTree :=
  match declaration with
  | Phase1RecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
      record =>
      phase1_surface_record_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
        record
  | Phase1DataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
      data_value =>
      phase1_surface_data_generic_requirement_expression_fallback_base_choice_shift_refined_spine_tree
        data_value
  end.

Definition
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
  (fuel : nat)
  (declaration : Phase1SurfaceDeclarationSpine)
  : option
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration :=
  match phase1_declaration_spine_tag declaration with
  | Phase1RecordDeclaration =>
      match
        phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
          fuel
          (phase1_declaration_spine_selected_tree declaration)
      with
      | Some record =>
          Some
            (Phase1RecordGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
              record)
      | None => None
      end
  | Phase1DataDeclaration =>
      match
        phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
          fuel
          (phase1_declaration_spine_selected_tree declaration)
      with
      | Some data_value =>
          Some
            (Phase1DataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
              data_value)
      | None => None
      end
  | _ => None
  end.

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_round_trip :
  forall fuel declaration refined,
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel
      fuel declaration = Some refined ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_tree
      refined =
    phase1_declaration_spine_selected_tree declaration.
Proof.
  intros fuel [tag selected_tree] refined Hnormalize.
  destruct tag; cbn in Hnormalize; try discriminate Hnormalize.
  - destruct
      (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel selected_tree)
      as [record |] eqn:Hrecord; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    eapply
      phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip.
    exact Hrecord.
  - destruct
      (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel selected_tree)
      as [data_value |] eqn:Hdata; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    eapply
      phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip.
    exact Hdata.
Qed.
