From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceImplementationCertificate.

Import ListNotations.

(*
  Erase the existential reference-source witness from the caller-facing
  certified record/data implementation correspondence evidence.

  #1522 returns exactly one corresponding implementation while retaining the
  normalized source existentially in the attached certificate. This slice
  projects that source-valued evidence down to the reconstructed certified tree:
  callers receive exactly one implementation plus a tree reconstructed by that
  implementation, returned by the certified reference parser, and carrying a
  complete derivation.

  Structural Rocq surface correspondence only. This preserves the existing
  record/data derivability premise, does not change Grammar-v1, add declaration
  families, extract or bind a Haskell parser, alter production parser behavior,
  or claim completeness beyond the existing derivable shift-refined record/data
  carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1522.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_tree_certificate :
  forall tokens,
    (exists source,
      phase1_surface_reference_source_top_level tokens = Some source /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
        source) ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      exists tree,
        phase1_surface_shift_refined_record_data_implementation_source_tree
          implementation = Some tree /\
        phase1_surface_reference_parse tokens =
          Some ([], ResultTree tree) /\
        Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens Htokens.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_certificate
      tokens Htokens)
    as
      [implementation
        [[Hcorresponds
          [source
            [Hsource
              [Hderive
                [Htree
                  [Hparse Hcomplete]]]]]]
          Himplementation_unique]].
  exists implementation.
  - split.
    + exact Hcorresponds.
    + exists (phase1_surface_source_top_level_tree source).
      repeat split.
      * exact Htree.
      * exact Hparse.
      * exact Hcomplete.
  - intros implementation'
      [Hcorresponds'
        [tree'
          [Htree'
            [Hparse' Hcomplete']]]].
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique.
    + exact Hcorresponds.
    + exact Hcorresponds'.
Qed.
