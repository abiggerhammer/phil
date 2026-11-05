From Phil.Surface Require Import GrammarAstRecordDataShiftRefinedCertified.

Theorem phase1_surface_reference_shift_refined_record_data_implementation_certified_tree_certificate_exists_unique :
  forall tokens implementation,
    phase1_surface_reference_shift_refined_record_data_implementation_certified tokens implementation ->
    exists! tree,
      phase1_surface_shift_refined_record_data_implementation_source_tree implementation = Some tree /\
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
      Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens implementation Hcertified.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_certified_tree_certificate
      tokens implementation Hcertified)
    as [tree [Htree [Hparse Hcomplete]]].
  exists tree.
  - repeat split; assumption.
  - intros tree' [Htree' _].
    rewrite Htree in Htree'.
    inversion Htree'.
    reflexivity.
Qed.
