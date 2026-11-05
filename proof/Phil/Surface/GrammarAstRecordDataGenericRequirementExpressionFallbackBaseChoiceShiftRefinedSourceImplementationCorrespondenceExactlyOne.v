From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondence.

(*
  Package the fuel-erased record/data surface correspondence as an exactly-one
  implementation result for every derivable reference source.

  #1516 exposes a functional, sound, and total correspondence relation while
  hiding the finite-fuel witness. This slice combines totality and functionality
  into the caller-facing uniqueness statement: a derivable reference source has
  exactly one corresponding implementation view, and that view reconstructs the
  exact source tree.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  add declaration families, extract or bind a Haskell parser, alter production
  parser behavior, or claim completeness beyond the existing derivable
  shift-refined record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1516.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_exactly_one :
  forall tokens source,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    exists! implementation,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation =
        Some (phase1_surface_source_top_level_tree source).
Proof.
  intros tokens source Hsource Hderive.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_total
      tokens source Hsource Hderive)
    as [implementation [Hcorresponds Htree]].
  exists implementation.
  - split.
    + exact Hcorresponds.
    + exact Htree.
  - intros implementation' [Hcorresponds' Htree'].
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique.
    + exact Hcorresponds.
    + exact Hcorresponds'.
Qed.
