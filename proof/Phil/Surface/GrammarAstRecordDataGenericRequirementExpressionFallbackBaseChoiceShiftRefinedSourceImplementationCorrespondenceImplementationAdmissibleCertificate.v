From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceImplementationAdmissibilityWitnessErasedCertificate.

Import ListNotations.

(*
  Package the caller-facing admissibility premise as a token-only proposition.

  #1525 removes the existential source witness but still exposes the reference
  parser match directly in the certificate premise. This slice names that
  match-indexed condition, proves it equivalent to the earlier existential
  derivable-reference-source formulation, and restates the exactly-one
  implementation certificate against the token-only admissibility interface.

  Structural Rocq surface correspondence only. This does not weaken the
  existing derivability requirement, change Grammar-v1, add declaration
  families, extract or bind a Haskell parser, alter production parser behavior,
  or claim completeness beyond the existing derivable shift-refined record/data
  carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1525.
*)

Definition
  phase1_surface_reference_shift_refined_record_data_admissible
  (tokens : list ConcreteToken)
  : Prop :=
  match phase1_surface_reference_source_top_level tokens with
  | Some source =>
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
        source
  | None => False
  end.

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_iff_source :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens <->
    exists source,
      phase1_surface_reference_source_top_level tokens = Some source /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
        source.
Proof.
  intros tokens.
  unfold phase1_surface_reference_shift_refined_record_data_admissible.
  destruct
    (phase1_surface_reference_source_top_level tokens)
    as [source |] eqn:Hsource.
  - split.
    + intro Hderive.
      exists source.
      split.
      * exact Hsource.
      * exact Hderive.
    + intros [source' [Hsource' Hderive]].
      rewrite Hsource in Hsource'.
      inversion Hsource'.
      subst source'.
      exact Hderive.
  - split.
    + contradiction.
    + intros [source [Hsource' Hderive]].
      rewrite Hsource in Hsource'.
      discriminate Hsource'.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_admissible_certificate :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
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
    phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_admissibility_witness_erased_certificate.
  exact Hadmissible.
Qed.
