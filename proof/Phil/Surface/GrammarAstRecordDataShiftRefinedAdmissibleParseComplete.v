From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataShiftRefinedAdmissibleTreeUnique.

Import ListNotations.

(*
  Project the complete-derivation witness from the token-only admissibility
  certificate onto an observed successful reference parse.

  #1532 proves that admissible shift-refined record/data token streams have a
  unique certified reference parse tree. This slice gives callers the direct
  elimination rule they need: if the reference parser returns a ResultTree for
  an admissible token stream, that exact tree carries Phase1CompleteDerivation.

  Structural Rocq surface refinement only. This does not change Grammar-v1,
  add declaration families, alter the Haskell/runtime parser, weaken
  admissibility, or extend completeness beyond the existing shift-refined
  record/data carrier. Continues PHIL-SURFACE-GRAMMAR-CORR-001 after #1532.
*)

Theorem
  phase1_surface_reference_shift_refined_record_data_admissible_parse_complete :
  forall tokens tree,
    phase1_surface_reference_shift_refined_record_data_admissible tokens ->
    phase1_surface_reference_parse tokens = Some ([], ResultTree tree) ->
    Phase1CompleteDerivation tokens tree.
Proof.
  intros tokens tree Hadmissible Hparse.
  destruct
    (phase1_surface_reference_shift_refined_record_data_admissible_tree_certificate_exists_unique
      tokens Hadmissible)
    as [canonical [[Hcanonical_parse Hcanonical_complete] Hcanonical_unique]].
  rewrite Hcanonical_parse in Hparse.
  inversion Hparse.
  subst tree.
  exact Hcanonical_complete.
Qed.
