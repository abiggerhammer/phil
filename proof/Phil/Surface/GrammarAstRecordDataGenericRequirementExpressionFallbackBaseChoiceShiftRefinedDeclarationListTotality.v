From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclarationList
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclarationTotality.

Import ListNotations.

(*
  Derivation-driven shared-fuel totality for finite lists of the shift-refined
  record/data declaration spines introduced through #1503.

  Each list member must already be certified as either an ordinary record_decl
  or data_decl derivation.  The existing declaration-level totality theorem
  provides a finite local witness; Nat.max plus the established single/list
  monotonicity lemmas raises the head and tail to one common fuel value.

  Structural Rocq surface correspondence only.  This does not add support for
  other declaration families, lift attributes/top-level/source carriers, change
  Grammar-v1, or alter runtime/extraction behavior.  Continues
  PHIL-SURFACE-GRAMMAR-CORR-001 after #1503.
*)

Definition
  phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_derivable
  (declaration : Phase1SurfaceDeclarationSpine)
  : Prop :=
  exists path input rest,
    (phase1_declaration_spine_tag declaration = Phase1RecordDeclaration /\
      Derives phase1_surface_rules path (ENonterminal "record_decl")
        input rest (phase1_declaration_spine_selected_tree declaration)) \/
    (phase1_declaration_spine_tag declaration = Phase1DataDeclaration /\
      Derives phase1_surface_rules path (ENonterminal "data_decl")
        input rest (phase1_declaration_spine_selected_tree declaration)).

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel_total :
  forall declarations,
    Forall
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_derivable
      declarations ->
    exists fuel refined,
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel
        fuel declarations = Some refined /\
      map
        phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_tree
        refined =
      map phase1_declaration_spine_selected_tree declarations.
Proof.
  intros declarations Hderive.
  induction Hderive as
    [|declaration declarations Hdeclaration Hdeclarations IH].
  - exists 0, [].
    split; reflexivity.
  - unfold
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_derivable
      in Hdeclaration.
    destruct Hdeclaration as
      [path [input [remaining Hdeclaration]]].
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_total_from_derivation
        path input remaining declaration Hdeclaration)
      as [declaration_fuel [refined_declaration [Hdeclaration_normalize Hdeclaration_tree]]].
    destruct IH as
      [rest_fuel [refined_rest [Hrest_normalize Hrest_trees]]].
    exists (Nat.max declaration_fuel rest_fuel),
      (refined_declaration :: refined_rest).
    split.
    + cbn.
      rewrite
        (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spine_fuel_monotone
          declaration_fuel
          (Nat.max declaration_fuel rest_fuel)
          declaration
          refined_declaration
          (Nat.le_max_l declaration_fuel rest_fuel)
          Hdeclaration_normalize).
      rewrite
        (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_declaration_spines_fuel_monotone
          rest_fuel
          (Nat.max declaration_fuel rest_fuel)
          declarations
          refined_rest
          (Nat.le_max_r declaration_fuel rest_fuel)
          Hrest_normalize).
      reflexivity.
    + cbn.
      rewrite Hdeclaration_tree.
      rewrite Hrest_trees.
      reflexivity.
Qed.
