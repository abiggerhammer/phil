From Stdlib Require Import Lists.List.
From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceImplementationCorrespondenceImplementationAdmissibleCertificate.
Import ListNotations.

Definition
  phase1_surface_reference_shift_refined_record_data_implementation_certified
  (tokens : list ConcreteToken)
  (implementation :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource)
  : Prop :=
  phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
    tokens implementation /\
  match
    phase1_surface_shift_refined_record_data_implementation_source_tree implementation
  with
  | Some tree =>
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
      Phase1CompleteDerivation tokens tree
  | None => False
  end.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_certified :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! implementation :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource,
      phase1_surface_reference_shift_refined_record_data_implementation_certified
        tokens implementation.
Proof.
  intros tokens Hadmissible.
  unfold phase1_surface_reference_shift_refined_record_data_implementation_certified.
  apply
    phase1_surface_reference_shift_refined_record_data_implementation_exists_unique_admissible_certificate.
  exact Hadmissible.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_unique :
  forall tokens implementation1 implementation2,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation1 ->
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation2 ->
    implementation1 = implementation2.
Proof.
  intros tokens implementation1 implementation2
    [Hcorresponds1 Hcertificate1]
    [Hcorresponds2 Hcertificate2].
  eapply
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_unique.
  - exact Hcorresponds1.
  - exact Hcorresponds2.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_iff_corresponds :
  forall tokens implementation,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation <->
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation.
Proof.
  intros tokens implementation.
  split.
  - intros [Hcorresponds Hcertificate].
    exact Hcorresponds.
  - intro Hcorresponds.
    split.
    + exact Hcorresponds.
    + destruct
        (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_sound
          tokens implementation Hcorresponds)
        as [refined [Himplementation [Htree [Hparse Hcomplete]]]].
      rewrite Htree.
      split.
      * exact Hparse.
      * exact Hcomplete.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_tree_certificate :
  forall tokens implementation,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation ->
    exists tree,
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation = Some tree /\
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
      Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens implementation [Hcorresponds Hcertificate].
  destruct
    (phase1_surface_shift_refined_record_data_implementation_source_tree
      implementation)
    as [tree |] eqn:Htree.
  - rewrite Htree in Hcertificate.
    exists tree.
    split.
    + exact Htree.
    + exact Hcertificate.
  - rewrite Htree in Hcertificate.
    contradiction.
Qed.
