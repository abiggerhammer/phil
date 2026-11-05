From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceCertificate.

Import ListNotations.

(*
  Package the fuel-erased record/data implementation correspondence and its
  certified reference-source evidence as one canonical caller-facing theorem.

  #1518 makes the correspondence itself exists-unique for every derivable
  shift-refined record/data reference source. #1519 shows that any such
  correspondence reconstructs the exact source tree and carries the matching
  certified reference parse and complete derivation evidence. This slice
  composes those results so proof clients receive existence, uniqueness,
  reconstruction, parsing, and derivation evidence in one certificate.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  add declaration families, extract or bind a Haskell parser, alter production
  parser behavior, or claim completeness beyond the existing derivable
  shift-refined record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1519.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_exists_unique_certificate :
  forall tokens source,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    exists! implementation,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
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
  intros tokens source Hsource Hderive.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_total
      tokens source Hsource Hderive)
    as [implementation [Hcorresponds Htree]].
  exists implementation.
  - pose proof
      (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_certifies_source
        tokens source implementation Hsource Hderive Hcorresponds)
      as [Htree_cert [Hparse Hcomplete]].
    repeat split.
    + exact Hcorresponds.
    + exact Htree_cert.
    + exact Hparse.
    + exact Hcomplete.
  - intros implementation' [Hcorresponds' [Htree' [Hparse' Hcomplete']]].
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique.
    + exact Hcorresponds.
    + exact Hcorresponds'.
Qed.
