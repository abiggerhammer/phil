From Phil.Surface Require Import
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyMutualPredictiveBridge.

(*
  Final discharge of PHIL-SURFACE-DETERM-001.

  #807 proves that every ordinary complete Grammar-v1 derivation is resolved
  by the single predictive oracle.  #554 proves that one oracle has at most one
  complete parse for a token stream.  Their composition is language-level
  surface parse uniqueness.
*)

Theorem phase1_surface_complete_derivation_unique :
  forall tokens firstTree secondTree,
    Phase1CompleteDerivation tokens firstTree ->
    Phase1CompleteDerivation tokens secondTree ->
    firstTree = secondTree.
Proof.
  intros tokens firstTree secondTree Hfirst Hsecond.
  eapply same_oracle_has_one_complete_parse
    with (oracle := phase1_surface_predictive_oracle)
         (tokens := tokens).
  - apply phase1_surface_complete_derivation_predictive_oracle.
    exact Hfirst.
  - apply phase1_surface_complete_derivation_predictive_oracle.
    exact Hsecond.
Qed.
