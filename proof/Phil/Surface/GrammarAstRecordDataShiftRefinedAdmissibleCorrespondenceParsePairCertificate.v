From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceParseWitness.

Import ListNotations.

(*
  Flatten the nested admissible implementation/tree witness from #1543 into a
  single jointly unique pair.

  #1543 exposes exactly one corresponding implementation and, for that
  implementation, exactly one concrete parse tree that is both its projected
  source tree and the certified reference parser's ResultTree. This slice
  packages those two witnesses as exactly one (implementation, ParseTree) pair
  so callers can destruct one certificate and retain joint uniqueness directly.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1543.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_correspondence_parse_pair_certificate_exists_unique :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! witness :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource *
      ParseTree,
      let '(implementation, tree) := witness in
      phase1_surface_reference_shift_refined_record_data_implementation_source_corresponds
        tokens implementation /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation = Some tree /\
      phase1_surface_reference_parse tokens = Some ([], ResultTree tree).
Proof.
  intros tokens Hadmissible.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_correspondence_parse_witness_exists_unique
      tokens Hadmissible)
    as
      [implementation
        [[Hcorresponds Htree_exists_unique]
          Himplementation_unique]].
  destruct Htree_exists_unique
    as [tree [[Hsource Hparse] Htree_unique]].
  exists (implementation, tree).
  - cbn.
    repeat split.
    + exact Hcorresponds.
    + exact Hsource.
    + exact Hparse.
  - intros [implementation' tree'].
    cbn.
    intros [Hcorresponds' [Hsource' Hparse']].
    assert (Himplementation_eq : implementation' = implementation).
    {
      apply Himplementation_unique.
      split.
      - exact Hcorresponds'.
      - exists tree'.
        + split.
          * exact Hsource'.
          * exact Hparse'.
        + intros tree'' [Hsource'' Hparse''].
          rewrite Hsource' in Hsource''.
          inversion Hsource''.
          reflexivity.
    }
    subst implementation'.
    assert (Htree_eq : tree' = tree).
    {
      apply Htree_unique.
      split.
      - exact Hsource'.
      - exact Hparse'.
    }
    subst tree'.
    reflexivity.
Qed.
