From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelList.

Import ListNotations.

(*
  Lift the finite-list shift-refined record/data top-level carrier through the
  existing whole-source module/import/declaration shell.

  Module and import headers remain represented by their already-proved source
  carriers.  Only the top-level declaration list is refined here, under one
  explicit fuel value.  Successful refinement reconstructs the exact original
  source ParseTree and is stable under larger fuel.

  Structural Rocq surface correspondence only.  This does not add other
  declaration families, prove source-level derivation-driven totality, change
  Grammar-v1, or alter Haskell/runtime/extraction/evaluation behavior.
  Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1508.
*)

Record
  Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSource
  : Type := {
  phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_module :
    option Phase1SurfaceNameList;
  phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_imports :
    list Phase1SurfaceImportHeader;
  phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_declarations :
    list
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelSpine
}.

Definition
  phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
  (source :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSource)
  : ParseTree :=
  PTNonterminal phase1_surface_start
    (PTSequence
      [ match
          phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_module
            source
        with
        | None => PTOptionalNone
        | Some name => PTOptionalSome (phase1_surface_module_decl_tree name)
        end;
        PTRepetition
          (map phase1_surface_import_decl_tree
            (phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_imports
              source));
        PTRepetition
          (map
            phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spine_tree
            (phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_declarations
              source))
      ]).

Definition
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
  (fuel : nat)
  (source : Phase1SurfaceSourceTopLevel)
  : option
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSource :=
  match
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
      fuel (phase1_source_top_level_declarations source)
  with
  | Some declarations =>
      Some
        {| phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_module :=
             phase1_source_top_level_module source;
           phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_imports :=
             phase1_source_top_level_imports source;
           phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_declarations :=
             declarations |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_round_trip :
  forall fuel source refined,
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
      fuel source = Some refined ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
      refined =
    phase1_surface_source_top_level_tree source.
Proof.
  intros fuel [module_name import_headers top_levels] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
      fuel top_levels)
    as [refined_top_levels |] eqn:Htop_levels;
    try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree.
  cbn.
  rewrite
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel_round_trip
      fuel top_levels refined_top_levels Htop_levels).
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_monotone :
  forall fuel larger source refined,
    fuel <= larger ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
      fuel source = Some refined ->
    phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
      larger source = Some refined.
Proof.
  intros fuel larger [module_name import_headers top_levels] refined Hle Hnormalize.
  cbn in Hnormalize |- *.
  destruct
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel
      fuel top_levels)
    as [refined_top_levels |] eqn:Htop_levels;
    try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  rewrite
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_spines_fuel_monotone
      fuel larger top_levels refined_top_levels Hle Htop_levels).
  reflexivity.
Qed.
