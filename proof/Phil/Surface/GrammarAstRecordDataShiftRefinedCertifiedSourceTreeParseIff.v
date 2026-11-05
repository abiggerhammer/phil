From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedCertified.

Import ListNotations.

Theorem
  phase1_surface_reference_shift_refined_record_data_implementation_certified_source_tree_parse_iff :
  forall tokens implementation,
    phase1_surface_reference_shift_refined_record_data_implementation_certified
      tokens implementation ->
    forall tree,
      (phase1_surface_shift_refined_record_data_implementation_source_tree
         implementation = Some tree <->
       phase1_surface_reference_parse tokens = Some ([], ResultTree tree)).
Proof.
  intros tokens implementation Hcertified tree.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_certified_tree_certificate
      tokens implementation Hcertified)
    as [certified_tree [Hsource [Hparse Hcomplete]]].
  split.
  - intro Hcandidate_source.
    rewrite Hsource in Hcandidate_source.
    inversion Hcandidate_source.
    exact Hparse.
  - intro Hcandidate_parse.
    rewrite Hparse in Hcandidate_parse.
    inversion Hcandidate_parse.
    exact Hsource.
Qed.
