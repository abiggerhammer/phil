From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceTotality.

(*
  Bind the whole-source shift-refined record/data carrier to the certified
  reference parser.

  The preceding source-totality slice proves that every already-normalized
  source whose top-level declarations are certified record_decl/data_decl
  derivations admits one finite fuel value for the shift-refined carrier. This
  slice threads that carrier through phase1_surface_reference_source_top_level:
  successful refinement is tied back to the exact certified complete parse tree,
  and derivable reference-parser sources are shown to admit some finite fuel.

  Structural Rocq surface correspondence only. This does not add the other
  declaration families, extract the carrier, connect it to the Haskell
  production AST, change Grammar-v1, or alter runtime/evaluation behavior.
  Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1510.
*)

Definition
  phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
  (fuel : nat)
  (tokens : list ConcreteToken)
  : option
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSource :=
  match phase1_surface_reference_source_top_level tokens with
  | Some source =>
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
        fuel source
  | None => None
  end.

Theorem
  phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_sound :
  forall fuel tokens refined,
    phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
      fuel tokens = Some refined ->
    exists source tree,
      phase1_surface_reference_source_top_level tokens = Some source /\
      phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
        fuel source = Some refined /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
        refined = tree /\
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
      Phase1CompleteDerivation tokens tree.
Proof.
  intros fuel tokens refined Hreference.
  unfold
    phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
    in Hreference.
  destruct (phase1_surface_reference_source_top_level tokens)
    as [source |] eqn:Hsource; try discriminate Hreference.
  destruct
    (phase1_surface_reference_source_top_level_sound tokens source Hsource)
    as [tree [Hparse [Hsource_tree Hcomplete]]].
  exists source, tree.
  repeat split.
  - exact Hsource.
  - exact Hreference.
  - rewrite
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_round_trip
        fuel source refined Hreference).
    exact Hsource_tree.
  - exact Hparse.
  - exact Hcomplete.
Qed.

Theorem
  phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_total :
  forall tokens source,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    exists fuel refined,
      phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
        fuel tokens = Some refined /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
        refined =
      phase1_surface_source_top_level_tree source.
Proof.
  intros tokens source Hsource Hderive.
  destruct
    (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_total
      source Hderive)
    as [fuel [refined [Hnormalize Htree]]].
  exists fuel, refined.
  split.
  - unfold
      phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel.
    rewrite Hsource.
    exact Hnormalize.
  - exact Htree.
Qed.
