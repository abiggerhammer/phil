From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleCorrespondenceParsePairCertificate
  GrammarAstRecordDataShiftRefinedCertified.

Import ListNotations.

(*
  Repackage the jointly unique admissible correspondence/parse pair from #1544
  at the stable certified-implementation boundary.

  #1544 gives exactly one (implementation, ParseTree) pair carrying intrinsic
  correspondence, exact implementation-source-tree reconstruction, and the
  certified reference parser ResultTree. #1529 already identifies intrinsic
  correspondence with the certified implementation predicate. This slice
  composes those interfaces so callers starting from token-level admissibility
  can destruct one jointly unique pair whose implementation is certified and
  whose projected source tree is exactly the paired ParseTree.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend correspondence beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1545.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_certified_parse_pair_certificate_exists_unique :
  forall tokens,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    exists! witness :
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource *
      ParseTree,
      let '(implementation, tree) := witness in
      phase1_surface_reference_shift_refined_record_data_implementation_certified
        tokens implementation /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation = Some tree.
Proof.
  intros tokens Hadmissible.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_correspondence_parse_pair_certificate_exists_unique
      tokens Hadmissible)
    as
      [[implementation tree]
        [[Hcorresponds [Hsource Hparse]] Hpair_unique]].
  exists (implementation, tree).
  - cbn.
    split.
    + apply
        (proj2
          (phase1_surface_reference_shift_refined_record_data_implementation_certified_iff_corresponds
            tokens implementation)).
      exact Hcorresponds.
    + exact Hsource.
  - intros [implementation' tree'].
    cbn.
    intros [Hcertified' Hsource'].
    apply Hpair_unique.
    cbn.
    pose proof
      (proj1
        (phase1_surface_reference_shift_refined_record_data_implementation_certified_iff_corresponds
          tokens implementation')
        Hcertified')
      as Hcorresponds'.
    split.
    + exact Hcorresponds'.
    + split.
      * exact Hsource'.
      * destruct Hcertified' as [Hcertified_corresponds Hcertificate].
        rewrite Hsource' in Hcertificate.
        exact (proj1 Hcertificate).
Qed.
