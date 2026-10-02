From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSource
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelListTotality.

(*
  Derivation-driven finite-fuel totality for the whole-source shift-refined
  record/data carrier introduced through #1509.

  A source is admissible here when every declaration in its top-level list is
  already certified as an ordinary record_decl or data_decl derivation.  The
  existing finite-list totality theorem supplies one shared fuel value for the
  declarations; module and import headers are preserved structurally by the
  source carrier.  The resulting refined source reconstructs the exact original
  source ParseTree.

  Structural Rocq surface correspondence only.  This does not add other
  declaration families, connect the carrier directly to the reference parser,
  change Grammar-v1, or alter Haskell/runtime/extraction/evaluation behavior.
  Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1509.
*)

Definition
  phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
  (source : Phase1SurfaceSourceTopLevel)
  : Prop :=
  Forall
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_derivable
    (phase1_source_top_level_declarations source).

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_total :
  forall source,
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    exists fuel refined,
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
        fuel source = Some refined /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
        refined =
      phase1_surface_source_top_level_tree source.
Proof.
  intros [module_name import_headers top_levels] Hderive.
  unfold
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
    in Hderive.
  cbn in Hderive.
  destruct
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel_total
      top_levels Hderive)
    as [fuel [refined_top_levels [Hnormalize Htrees]]].
  exists fuel.
  exists
    {| phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_module :=
         module_name;
       phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_imports :=
         import_headers;
       phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_declarations :=
         refined_top_levels |}.
  split.
  - cbn.
    rewrite Hnormalize.
    reflexivity.
  - unfold
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree.
    cbn.
    rewrite Htrees.
    reflexivity.
Qed.
