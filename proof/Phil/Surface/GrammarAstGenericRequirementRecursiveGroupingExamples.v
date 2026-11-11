From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstEffectSetRecursiveGroupingExamples
  GrammarAstGenericRequirementRecursiveGroupingSpine
  GrammarAstGenericRequirementRecursiveGroupingSpineTotality.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001: source-order, name, syntax, legacy
   preservation, and negative examples for the thirteen-way lift. *)

Definition phase1_generic_requirement_grouping_name : ParseTree :=
  phase1_surface_identifier_tree "capability".

Definition phase1_generic_requirement_grouping_example
  (effects : ParseTree) : ParseTree :=
  PTNonterminal "generic_requirement"
    (PTAlternative 6
      (PTSequence
        [ PTLiteral "effects";
          phase1_generic_requirement_grouping_name;
          PTLiteral "within";
          effects;
          PTLiteral ";" ])).

Example phase1_generic_requirement_grouping_preserves_empty_braces :
  match phase1_surface_normalize_generic_requirement_recursive_grouping_tree
    (phase1_generic_requirement_grouping_example
      (phase1_effect_set_grouping_example_literal_choice
        (phase1_effect_set_grouping_example_literal []))) with
  | Some (Phase1GenericEffectsRecursiveGroupingRequirement name
            (Phase1EffectSetGroupingLiteral literal)) =>
      name = phase1_generic_requirement_grouping_name /\
      phase1_effect_set_literal_recursive_grouping_spine_effects literal = []
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example phase1_generic_requirement_grouping_preserves_all_members :
  match phase1_surface_normalize_generic_requirement_recursive_grouping_tree
    (phase1_generic_requirement_grouping_example
      (phase1_effect_set_grouping_example_literal_choice
        phase1_effect_set_grouping_example_mixed_literal)) with
  | Some (Phase1GenericEffectsRecursiveGroupingRequirement name
            (Phase1EffectSetGroupingLiteral literal)) =>
      name = phase1_generic_requirement_grouping_name /\
      phase1_effect_set_grouping_has_all_members literal
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_generic_requirement_grouping_preserves_whole_tree :
  match phase1_surface_normalize_generic_requirement_recursive_grouping_tree
    (phase1_generic_requirement_grouping_example
      phase1_effect_set_grouping_example_reference_choice) with
  | Some refined =>
      phase1_surface_generic_requirement_recursive_grouping_spine_tree refined =
        phase1_generic_requirement_grouping_example
          phase1_effect_set_grouping_example_reference_choice
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_generic_requirement_grouping_legacy_reference_keeps_name :
  phase1_surface_refine_generic_requirement_recursive_grouping
    (Phase1GenericEffectsExpressionFallbackBaseChoiceShiftRefinedRequirement
      phase1_generic_requirement_grouping_name
      (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedReference
        phase1_effect_grouping_example_reference)) =
    Some (Phase1GenericEffectsRecursiveGroupingRequirement
      phase1_generic_requirement_grouping_name
      (Phase1EffectSetGroupingReference
        phase1_effect_grouping_example_reference)).
Proof. reflexivity. Qed.

Example phase1_generic_requirement_grouping_legacy_empty_literal :
  phase1_surface_refine_generic_requirement_recursive_grouping
    (Phase1GenericEffectsExpressionFallbackBaseChoiceShiftRefinedRequirement
      phase1_generic_requirement_grouping_name
      (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedLiteral
        {| phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects := [] |})) =
    Some (Phase1GenericEffectsRecursiveGroupingRequirement
      phase1_generic_requirement_grouping_name
      (Phase1EffectSetGroupingLiteral
        {| phase1_effect_set_literal_recursive_grouping_spine_effects := [] |})).
Proof. reflexivity. Qed.

Example phase1_generic_requirement_grouping_legacy_other_branch_unchanged :
  phase1_surface_refine_generic_requirement_recursive_grouping
    (Phase1GenericStructuralExpressionFallbackBaseChoiceShiftRefinedRequirement
      (PTLiteral "unmodified")) =
    Some (Phase1GenericStructuralRecursiveGroupingRequirement
      (PTLiteral "unmodified")).
Proof. reflexivity. Qed.

Example phase1_generic_requirement_grouping_rejects_wrong_within :
  phase1_surface_normalize_generic_requirement_recursive_grouping_tree
    (PTNonterminal "generic_requirement"
      (PTAlternative 6
        (PTSequence
          [ PTLiteral "effects";
            phase1_generic_requirement_grouping_name;
            PTLiteral "outside";
            phase1_effect_set_grouping_example_reference_choice;
            PTLiteral ";" ]))) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_generic_requirement_grouping_rejects_wrong_alternative :
  phase1_surface_normalize_generic_requirement_recursive_grouping_tree
    (PTNonterminal "generic_requirement"
      (PTAlternative 13
        (PTSequence
          [ PTLiteral "effects";
            phase1_generic_requirement_grouping_name;
            PTLiteral "within";
            phase1_effect_set_grouping_example_reference_choice;
            PTLiteral ";" ]))) = None.
Proof. vm_compute. reflexivity. Qed.
