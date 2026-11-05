From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceSourceErasedCertificate.

Import ListNotations.

(*
  Erase the explicit source component from the caller-facing certified
  record/data implementation correspondence result.

  #1521 removes the need for callers to choose a source witness before obtaining
  the canonical source/implementation certificate. This slice projects that
  certificate onto the implementation itself: every admissible token stream has
  exactly one corresponding implementation, while the exact normalized source,
  source-tree reconstruction, certified reference parse, and complete derivation
  remain available existentially as evidence attached to that implementation.

  Structural Rocq surface correspondence only. This does not weaken or remove
  the existing record/data derivability premise, add declaration families,
  extract or bind a Haskell parser, alter production parser behavior, or claim
  completeness beyond the existing derivable shift-refined record/data carrier.
  Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1521.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_certificate :
  forall tokens,
    (exists source,
      phase1_surface_reference_source_top_level tokens = Some source /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
        source) ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      exists source,
        phase1_surface_reference_source_top_level tokens = Some source /\
        phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
          source /\
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
  intros tokens Htokens.
  destruct
    (phase1_surface_reference_shift_refined_record_data_source_implementation_exists_unique_certificate
      tokens Htokens)
    as
      [[source implementation]
        [Hcertificate Hpair_unique]].
  cbn in Hcertificate.
  destruct Hcertificate as
    [Hsource
      [Hderive
        [Hcorresponds
          [Htree
            [Hparse Hcomplete]]]]].
  exists implementation.
  - split.
    + exact Hcorresponds.
    + exists source.
      repeat split.
      * exact Hsource.
      * exact Hderive.
      * exact Htree.
      * exact Hparse.
      * exact Hcomplete.
  - intros implementation'
      [Hcorresponds'
        [source'
          [Hsource'
            [Hderive'
              [Htree'
                [Hparse' Hcomplete']]]]]].
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique.
    + exact Hcorresponds.
    + exact Hcorresponds'.
Qed.
