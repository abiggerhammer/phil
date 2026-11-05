From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationRepresentation.

Import ListNotations.

(*
  Close the remaining caller-visible proof-carrier seam between the certified
  reference parser and the shift-refined record/data implementation view.

  #1512 provides a lossless implementation-facing representation once a
  shift-refined whole-source carrier already exists.  This slice composes that
  representation bridge with the finite-fuel certified reference normalizer so
  callers can ask directly for an implementation view from tokens.

  Successful direct normalization is tied back to the exact refined source,
  exact reconstructed ParseTree, reference-parser success, and complete
  derivation.  Conversely, every derivable record/data reference source admits
  some finite fuel producing an implementation view that reconstructs the same
  source tree.

  Structural Rocq surface correspondence only.  This does not extract a
  Haskell kernel, bind the production AST, add other declaration families,
  change Grammar-v1, or alter runtime/evaluation behavior.  Continues
  PHIL-SURFACE-GRAMMAR-CORR-001 after #1512.
*)

Definition
  phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
  (fuel : nat)
  (tokens : list ConcreteToken)
  : option
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource :=
  match
    phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
      fuel tokens
  with
  | Some refined =>
      Some
        (phase1_surface_shift_refined_record_data_source_to_implementation
          refined)
  | None => None
  end.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_sound :
  forall fuel tokens implementation,
    phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
      fuel tokens = Some implementation ->
    exists refined,
      phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
        fuel tokens = Some refined /\
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
  intros fuel tokens implementation Himplementation.
  unfold
    phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
    in Himplementation.
  destruct
    (phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
      fuel tokens)
    as [refined |] eqn:Hrefined; try discriminate Himplementation.
  inversion Himplementation; subst implementation.
  destruct
    (phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_sound
      fuel tokens refined Hrefined)
    as
      [source
        [tree
          [Hsource
            [Hnormalize
              [Htree
                [Hparse Hcomplete]]]]]].
  exists refined.
  repeat split.
  - exact Hrefined.
  - reflexivity.
  - apply
      phase1_surface_shift_refined_record_data_implementation_source_tree_round_trip.
  - rewrite Htree.
    exact Hparse.
  - rewrite Htree.
    exact Hcomplete.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_fuel_total :
  forall tokens source,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    exists fuel refined implementation,
      phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
        fuel tokens = Some refined /\
      phase1_surface_reference_shift_refined_record_data_implementation_source_fuel
        fuel tokens = Some implementation /\
      implementation =
        phase1_surface_shift_refined_record_data_source_to_implementation
          refined /\
      phase1_surface_shift_refined_record_data_source_from_implementation
        implementation = Some refined /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation =
        Some (phase1_surface_source_top_level_tree source).
Proof.
  intros tokens source Hsource Hderive.
  destruct
    (phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_total
      tokens source Hsource Hderive)
    as [fuel [refined [Hrefined Htree]]].
  exists fuel, refined,
    (phase1_surface_shift_refined_record_data_source_to_implementation refined).
  repeat split.
  - exact Hrefined.
  - unfold
      phase1_surface_reference_shift_refined_record_data_implementation_source_fuel.
    rewrite Hrefined.
    reflexivity.
  - reflexivity.
  - apply
      phase1_surface_shift_refined_record_data_source_implementation_round_trip.
  - rewrite
      phase1_surface_shift_refined_record_data_implementation_source_tree_round_trip.
    rewrite Htree.
    reflexivity.
Qed.
