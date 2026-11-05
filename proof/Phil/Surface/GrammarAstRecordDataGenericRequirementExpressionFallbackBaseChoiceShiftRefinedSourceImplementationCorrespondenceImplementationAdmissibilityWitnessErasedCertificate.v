From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceImplementationTreeWitnessErasedCertificate.

Import ListNotations.

(*
  Erase the remaining existential source witness from the caller-facing
  admissibility premise for the certified record/data implementation
  correspondence.

  #1524 removes the separate tree witness from the result while retaining an
  existential source witness in the premise. This slice projects that premise
  onto the actual result of phase1_surface_reference_source_top_level: when it
  returns a source, that exact source must satisfy the existing shift-refined
  record/data derivability predicate; when it returns None, the premise is
  false. Callers therefore no longer choose or package a source witness.

  Structural Rocq surface correspondence only. This preserves the existing
  derivability requirement, does not change Grammar-v1, add declaration
  families, extract or bind a Haskell parser, alter production parser behavior,
  or claim completeness beyond the existing derivable shift-refined record/data
  carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1524.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_admissibility_witness_erased_certificate :
  forall tokens,
    match phase1_surface_reference_source_top_level tokens with
    | Some source =>
        phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
          source
    | None => False
    end ->
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
  intros tokens Hadmissible.
  apply
    phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_tree_witness_erased_certificate.
  destruct
    (phase1_surface_reference_source_top_level tokens)
    as [source |] eqn:Hsource.
  - cbn in Hadmissible.
    exists source.
    split.
    + exact Hsource.
    + exact Hadmissible.
  - cbn in Hadmissible.
    contradiction.
Qed.
