From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceCanonicalCertificate.

Import ListNotations.

(*
  Erase the explicit source witness from the canonical fuel-erased record/data
  implementation correspondence certificate.

  #1520 packages existence, uniqueness, exact source-tree reconstruction,
  certified reference parsing, and complete derivation evidence once a
  derivable reference source is supplied. This slice lifts that certificate one
  step outward: when tokens admit any derivable certified reference source,
  there is exactly one source/implementation pair carrying the full canonical
  certificate. Callers therefore no longer need to choose a source witness
  before using the correspondence result.

  Structural Rocq surface correspondence only. This does not change Grammar-v1,
  add declaration families, extract or bind a Haskell parser, alter production
  parser behavior, or claim completeness beyond the existing derivable
  shift-refined record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001
  after #1520.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_source_implementation_exists_unique_certificate :
  forall tokens,
    (exists source,
      phase1_surface_reference_source_top_level tokens = Some source /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
        source) ->
    exists! witness :
      Phase1SurfaceSourceTopLevel *
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      let '(source, implementation) := witness in
      phase1_surface_reference_source_top_level tokens = Some source /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
        source /\
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
  intros tokens [source [Hsource Hderive]].
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_exists_unique_certificate
      tokens source Hsource Hderive)
    as
      [implementation
        [[Hcorresponds [Htree [Hparse Hcomplete]]]
          Himplementation_unique]].
  exists (source, implementation).
  - cbn.
    repeat split.
    + exact Hsource.
    + exact Hderive.
    + exact Hcorresponds.
    + exact Htree.
    + exact Hparse.
    + exact Hcomplete.
  - intros [source' implementation'].
    cbn.
    intros
      [Hsource'
        [Hderive'
          [Hcorresponds'
            [Htree'
              [Hparse' Hcomplete']]]]].
    assert (Hsource_eq : source = source').
    {
      rewrite Hsource in Hsource'.
      injection Hsource' as Hsource_eq.
      exact Hsource_eq.
    }
    subst source'.
    pose proof
      (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique
        tokens implementation implementation' Hcorresponds Hcorresponds')
      as Himplementation_eq.
    subst implementation'.
    reflexivity.
Qed.
