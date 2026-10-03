From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationNormalizationFuelStability.

Import ListNotations.

(*
  Erase the explicit-fuel choice from the caller-visible record/data
  token-to-implementation correspondence.

  #1515 proves that successful fuel choices are unique in result and that
  every derivable reference source is eventually stable. This slice packages
  the direct normalizer as a fuel-hidden correspondence relation and proves
  that relation functional, sound with respect to the certified reference
  parser, and total for the existing derivable shift-refined record/data
  source carrier.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  add declaration families, extract or bind a Haskell parser, alter production
  parser behavior, or claim completeness beyond the existing record/data
  shift-refined carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1515.
*)

Definition
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
  (tokens : list ConcreteToken)
  (implementation :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource)
  : Prop :=
  exists fuel,
    phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
      fuel tokens = Some implementation.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique :
  forall tokens implementation1 implementation2,
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation1 ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation2 ->
    implementation1 = implementation2.
Proof.
  intros tokens implementation1 implementation2
    [fuel1 Himplementation1] [fuel2 Himplementation2].
  eapply
    phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_unique.
  - exact Himplementation1.
  - exact Himplementation2.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_sound :
  forall tokens implementation,
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation ->
    exists refined,
      implementation =
        phase1_surface_shift_refined_record_data_source_to_implementation
          refined /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation =
        Some
          (phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
            refined) /\
      phase1_surface_reference_parse tokens =
        Some
          ([],
           ResultTree
             (phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
               refined)) /\
      Phase1CompleteDerivation tokens
        (phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
          refined).
Proof.
  intros tokens implementation [fuel Himplementation].
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_sound
      fuel tokens implementation Himplementation)
    as
      [refined
        [Hrefined
          [Himplementation_eq
            [Htree
              [Hparse Hcomplete]]]]].
  exists refined.
  repeat split.
  - exact Himplementation_eq.
  - exact Htree.
  - exact Hparse.
  - exact Hcomplete.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_total :
  forall tokens source,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    exists implementation,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation =
        Some (phase1_surface_source_top_level_tree source).
Proof.
  intros tokens source Hsource Hderive.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_total
      tokens source Hsource Hderive)
    as
      [fuel
        [refined
          [implementation
            [Hrefined
              [Himplementation
                [Himplementation_eq
                  [Hround_trip Htree]]]]]]].
  exists implementation.
  split.
  - exists fuel.
    exact Himplementation.
  - exact Htree.
Qed.
