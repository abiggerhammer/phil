From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceReconstruction.

Import ListNotations.

(*
  Collapse the fuel-erased record/data implementation correspondence onto the
  exact certified reference source.

  #1518 makes source-tree reconstruction intrinsic to the correspondence.
  This slice composes that result with the existing correspondence soundness
  theorem so callers receive one direct certificate: the implementation
  reconstructs the exact reference source tree, the certified reference parser
  returns that same tree, and the tree carries a complete derivation.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  add declaration families, extract or bind a Haskell parser, alter production
  parser behavior, or claim completeness beyond the existing derivable
  shift-refined record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1518.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_certifies_source :
  forall tokens source implementation,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation ->
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation =
      Some (phase1_surface_source_top_level_tree source) /\
    phase1_surface_reference_parse tokens =
      Some
        ([],
         ResultTree (phase1_surface_source_top_level_tree source)) /\
    Phase1CompleteDerivation tokens
      (phase1_surface_source_top_level_tree source).
Proof.
  intros tokens source implementation Hsource Hderive Hcorresponds.
  pose proof
    (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_reconstructs_source
      tokens source implementation Hsource Hderive Hcorresponds)
    as Hreconstruct.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_sound
      tokens implementation Hcorresponds)
    as [refined [Himplementation [Htree [Hparse Hcomplete]]]].
  rewrite Hreconstruct in Htree.
  injection Htree as Htrees.
  split.
  - exact Hreconstruct.
  - split.
    + rewrite Htrees.
      exact Hparse.
    + rewrite Htrees.
      exact Hcomplete.
Qed.
