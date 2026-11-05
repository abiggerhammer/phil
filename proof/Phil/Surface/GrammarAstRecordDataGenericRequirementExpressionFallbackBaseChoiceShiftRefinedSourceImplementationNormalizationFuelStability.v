From Stdlib Require Import Arith.PeanoNat Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationNormalizationFuelMonotonicity.

(*
  Close the explicit-fuel API seam for the direct record/data
  reference-to-implementation surface correspondence.

  #1513 establishes soundness and finite-fuel existence for the direct
  token-to-implementation normalizer. #1514 establishes upward stability once
  a fuel value succeeds. This slice packages those facts into two caller-facing
  consequences: successful results are independent of the successful fuel
  chosen, and every derivable reference source reaches a threshold after which
  all larger fuel values return the same implementation view.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  add declaration families, extract or bind a Haskell parser, alter production
  parser behavior, or claim completeness beyond the existing record/data
  shift-refined carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1514.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_unique :
  forall fuel1 fuel2 tokens implementation1 implementation2,
    phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
      fuel1 tokens = Some implementation1 ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
      fuel2 tokens = Some implementation2 ->
    implementation1 = implementation2.
Proof.
  intros fuel1 fuel2 tokens implementation1 implementation2 H1 H2.
  pose proof
    (phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_monotone
      fuel1 (Nat.max fuel1 fuel2) tokens implementation1
      (Nat.le_max_l fuel1 fuel2) H1)
    as H1max.
  pose proof
    (phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_monotone
      fuel2 (Nat.max fuel1 fuel2) tokens implementation2
      (Nat.le_max_r fuel1 fuel2) H2)
    as H2max.
  rewrite H1max in H2max.
  inversion H2max.
  reflexivity.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_eventually_stable :
  forall tokens source,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    exists threshold implementation,
      phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
        threshold tokens = Some implementation /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation =
        Some (phase1_surface_source_top_level_tree source) /\
      forall larger,
        threshold <= larger ->
        phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
          larger tokens = Some implementation.
Proof.
  intros tokens source Hsource Hderive.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_total
      tokens source Hsource Hderive)
    as
      [threshold
        [refined
          [implementation
            [Hrefined
              [Himplementation
                [Himplementation_eq
                  [Hround_trip Htree]]]]]]].
  exists threshold, implementation.
  repeat split.
  - exact Himplementation.
  - exact Htree.
  - intros larger Hle.
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_monotone.
    + exact Hle.
    + exact Himplementation.
Qed.
