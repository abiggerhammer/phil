From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationNormalization.

Import ListNotations.

(*
  Make #1513's direct reference-to-implementation normalizer upward-stable in
  its explicit fuel bound.

  The whole-source shift-refined normalizer already proves that a successful
  result at one fuel remains exactly the same result at every larger fuel.
  #1513 then wraps that certified source result in the lossless implementation
  representation.  This slice composes those facts at the caller-visible
  token-to-implementation boundary.

  Structural Rocq surface correspondence only.  This does not change
  Grammar-v1, add declaration families, extract or bind a Haskell parser,
  alter runtime/evaluation behavior, or claim completeness beyond the existing
  record/data shift-refined carrier.  Continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1513.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_monotone :
  forall fuel larger tokens implementation,
    fuel <= larger ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
      fuel tokens = Some implementation ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
      larger tokens = Some implementation.
Proof.
  intros fuel larger tokens implementation Hle Himplementation.
  unfold
    phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
    in Himplementation |- *.
  destruct
    (phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
      fuel tokens)
    as [refined |] eqn:Hrefined; try discriminate Himplementation.
  inversion Himplementation; subst implementation.
  unfold
    phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
    in Hrefined |- *.
  destruct (phase1_surface_reference_source_top_level tokens)
    as [source |] eqn:Hsource.
  - cbn in Hrefined |- *.
    rewrite
      (phase1_surface_normalize_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_monotone
        fuel larger source refined Hle Hrefined).
    reflexivity.
  - discriminate Hrefined.
Qed.
