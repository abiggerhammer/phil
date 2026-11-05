From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleImplementationCorrespondence
  GrammarAstRecordDataShiftRefinedAdmissibleTreeUnique.

Import ListNotations.

(*
  Pin any caller-held implementation correspondence for an admissible
  shift-refined record/data token stream to the unique canonical reference
  parse tree.

  #1537 exposes the exactly-one fuel-erased implementation correspondence from
  token-level admissibility, but callers that already hold a correspondence
  witness still have to recover its parse-tree consequence separately. This
  slice packages that consequence: the implementation reconstructs a tree that
  the certified reference parser returns with a complete derivation, and that
  tree is the unique such admissible reference tree.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1537.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_correspondence_canonical_tree_certificate :
  forall tokens implementation,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
      tokens implementation ->
    exists tree,
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation = Some tree /\
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree) /\
      Phase1CompleteDerivation tokens tree /\
      forall tree',
        phase1_surface_reference_parse tokens = Some ([], ResultTree tree') ->
        Phase1CompleteDerivation tokens tree' ->
        tree' = tree.
Proof.
  intros tokens implementation Hadmissible Hcorresponds.
  destruct
    (phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds_sound
      tokens implementation Hcorresponds)
    as [refined [Himplementation [Htree [Hparse Hcomplete]]]].
  exists
    (phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
      refined).
  repeat split.
  - exact Htree.
  - exact Hparse.
  - exact Hcomplete.
  - intros tree' Hparse' Hcomplete'.
    destruct
      (phase1_surface_reference_shift_refined_record_data_admissible_tree_certificate_exists_unique
        tokens Hadmissible)
      as [canonical [[Hcanonical_parse Hcanonical_complete] Hcanonical_unique]].
    assert
      (Htree_canonical :
        phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
          refined = canonical).
    {
      apply Hcanonical_unique.
      split.
      - exact Hparse.
      - exact Hcomplete.
    }
    assert (Htree'_canonical : tree' = canonical).
    {
      apply Hcanonical_unique.
      split.
      - exact Hparse'.
      - exact Hcomplete'.
    }
    rewrite Htree'_canonical.
    symmetry.
    exact Htree_canonical.
Qed.
