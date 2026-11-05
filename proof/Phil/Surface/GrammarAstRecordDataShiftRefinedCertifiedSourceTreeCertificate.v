From Stdlib Require Import Lists.List.
From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertifiedSourceTreeParseIff
  GrammarAstRecordDataShiftRefinedCertifiedSourceTreeComplete.
Import ListNotations.

Theorem phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_certificate :
  forall tokens implementation tree,
    phase1_surface_reference_shift_refined_record_data_implementation_certified tokens implementation ->
    phase1_surface_shift_refined_record_data_implementation_source_tree implementation = Some tree ->
    phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
    Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens implementation tree Hcertified Hsource.
  split.
  - apply (proj1
      (phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_parse_iff
        tokens implementation Hcertified tree)).
    exact Hsource.
  - eapply phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_complete;
      eauto.
Qed.

(*
  Package #1556's forward source-tree certificate and #1551's reverse
  parser-result transport as one complete characterization for callers that
  already hold a certified implementation.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_complete_iff :
  forall tokens implementation tree,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation ->
    (phase1_surface_shift_refined_record_data_implementation_source_tree
       implementation = Some tree <->
     phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
     Phase1CompleteDerivation tokens tree).
Proof.
  intros tokens implementation tree Hcertified.
  split.
  - intro Hsource.
    eapply
      phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_certificate;
      eauto.
  - intros [Hparse _].
    apply
      (proj2
        (phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_parse_iff
          tokens implementation Hcertified tree)).
    exact Hparse.
Qed.
