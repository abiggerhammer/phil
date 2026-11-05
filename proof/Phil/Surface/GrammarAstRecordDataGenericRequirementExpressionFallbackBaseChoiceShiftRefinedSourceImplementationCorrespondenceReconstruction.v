From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceExactlyOne.

(*
  Make exact source-tree reconstruction intrinsic to the fuel-erased
  record/data implementation correspondence.

  #1517 packages correspondence together with an explicit reconstruction
  conjunct as an exactly-one result. This slice shows callers do not need to
  carry that conjunct separately: once the certified reference parser identifies
  a derivable shift-refined record/data source, every corresponding
  implementation necessarily reconstructs that exact source tree. It then
  packages the correspondence relation itself as an exists!-unique result.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  add declaration families, extract or bind a Haskell parser, alter production
  parser behavior, or claim completeness beyond the existing derivable
  shift-refined record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1517.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_reconstructs_source :
  forall tokens source implementation,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation ->
    phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation =
      Some (phase1_surface_source_top_level_tree source).
Proof.
  intros tokens source implementation Hsource Hderive Hcorresponds.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_total
      tokens source Hsource Hderive)
    as [canonical [Hcanonical Htree]].
  pose proof
    (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique
      tokens implementation canonical Hcorresponds Hcanonical)
    as Heq.
  subst canonical.
  exact Htree.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_exists_unique :
  forall tokens source,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    exists! implementation,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation.
Proof.
  intros tokens source Hsource Hderive.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_total
      tokens source Hsource Hderive)
    as [implementation [Hcorresponds Htree]].
  exists implementation.
  - exact Hcorresponds.
  - intros implementation' Hcorresponds'.
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique.
    + exact Hcorresponds.
    + exact Hcorresponds'.
Qed.
