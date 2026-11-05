From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceImplementationTreeCertificate.

Import ListNotations.

(*
  Erase the remaining existential tree witness from the caller-facing certified
  record/data implementation correspondence evidence.

  #1523 returns exactly one corresponding implementation while retaining its
  reconstructed certified tree existentially. This slice projects that evidence
  into a match-indexed certificate on the implementation's own reconstruction
  result: callers no longer need to choose or unpack a separate tree witness.
  When reconstruction succeeds, that exact tree is returned by the certified
  reference parser and carries a complete derivation.

  Structural Rocq surface correspondence only. This preserves the existing
  record/data derivability premise, does not change Grammar-v1, add declaration
  families, extract or bind a Haskell parser, alter production parser behavior,
  or claim completeness beyond the existing derivable shift-refined record/data
  carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1523.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_tree_witness_erased_certificate :
  forall tokens,
    (exists source,
      phase1_surface_reference_source_top_level tokens = Some source /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
        source) ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      match
        phase1_surface_shift_refined_record_data_implementation_source_tree
          implementation
      with
      | Some tree =>
          phase1_surface_reference_parse tokens =
            Some ([], ResultTree tree) /\
          Phase1CompleteDerivation tokens tree
      | None => False
      end.
Proof.
  intros tokens Htokens.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_tree_certificate
      tokens Htokens)
    as
      [implementation
        [[Hcorresponds
          [tree
            [Htree
              [Hparse Hcomplete]]]]
          Himplementation_unique]].
  exists implementation.
  - split.
    + exact Hcorresponds.
    + rewrite Htree.
      split.
      * exact Hparse.
      * exact Hcomplete.
  - intros implementation' [Hcorresponds' Hcertificate'].
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique.
    + exact Hcorresponds.
    + exact Hcorresponds'.
Qed.
