From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelList
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelTotality.

Import ListNotations.

(*
  Derivation-driven shared-fuel totality for finite lists of the shift-refined
  record/data top-level declaration spines introduced through #1507.

  Each top-level list member must already carry a declaration certified as
  either an ordinary record_decl or data_decl derivation.  The existing
  top-level totality theorem supplies a finite local witness, and Nat.max plus
  the established single/list monotonicity lemmas raises the head and tail to
  one common fuel value while preserving the exact original top-level trees.

  Structural Rocq surface correspondence only.  This does not add other
  declaration families, lift the whole-source carrier, change Grammar-v1, or
  alter runtime/extraction/evaluation behavior.  Continues
  PHIL-SURFACE-GRAMMAR-CORR-001 after #1507.
*)

Definition
  phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_derivable
  (top_level : Phase1SurfaceTopLevelSpine)
  : Prop :=
  exists path input rest,
    (phase1_declaration_spine_tag
       (phase1_top_level_spine_declaration top_level) =
       Phase1RecordDeclaration /\
      Derives phase1_surface_rules path (ENonterminal "record_decl")
        input rest
        (phase1_declaration_spine_selected_tree
          (phase1_top_level_spine_declaration top_level))) \/
    (phase1_declaration_spine_tag
       (phase1_top_level_spine_declaration top_level) =
       Phase1DataDeclaration /\
      Derives phase1_surface_rules path (ENonterminal "data_decl")
        input rest
        (phase1_declaration_spine_selected_tree
          (phase1_top_level_spine_declaration top_level))).

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel_total :
  forall top_levels,
    Forall
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_derivable
      top_levels ->
    exists fuel refined,
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
        fuel top_levels = Some refined /\
      map
        phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_tree
        refined =
      map phase1_surface_top_level_spine_tree top_levels.
Proof.
  intros top_levels Hderive.
  induction Hderive as
    [|top_level top_levels Htop_level Htop_levels IH].
  - exists 0, [].
    split; reflexivity.
  - unfold
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_derivable
      in Htop_level.
    destruct Htop_level as
      [path [input [remaining Htop_level]]].
    destruct
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel_total_from_declaration_derivation
        path input remaining top_level Htop_level)
      as [top_level_fuel [refined_top_level [Htop_level_normalize Htop_level_tree]]].
    destruct IH as
      [rest_fuel [refined_rest [Hrest_normalize Hrest_trees]]].
    exists (Nat.max top_level_fuel rest_fuel),
      (refined_top_level :: refined_rest).
    split.
    + cbn.
      rewrite
        (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_fuel_monotone
          top_level_fuel
          (Nat.max top_level_fuel rest_fuel)
          top_level
          refined_top_level
          (Nat.le_max_l top_level_fuel rest_fuel)
          Htop_level_normalize).
      rewrite
        (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel_monotone
          rest_fuel
          (Nat.max top_level_fuel rest_fuel)
          top_levels
          refined_rest
          (Nat.le_max_r top_level_fuel rest_fuel)
          Hrest_normalize).
      reflexivity.
    + cbn.
      rewrite Htop_level_tree.
      rewrite Hrest_trees.
      reflexivity.
Qed.
