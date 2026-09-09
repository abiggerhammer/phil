from pathlib import Path

surface = Path("proof/Phil/Surface")

# The raw-rank bounded-sufficiency proof is logically complete, but Rocq 9.2
# and 9.3-rc1 both spend more than five minutes sealing its nonterminal theorem
# after every tactic has already succeeded.  The value-rank proof in
# GrammarParserTotalFuelValue.v proves the same parser-completeness statements
# without carrying the problematic rank equality through recursive theorem
# interfaces.  Keep the old split module names as lightweight compatibility
# shims, and make the canonical public module a facade over the kernel-friendly
# proof.

shim = r'''From Phil.Surface Require Export GrammarParserTotalFuelValue.
'''

(surface / "GrammarParserTotalFuelBase.v").write_text(shim)
(surface / "GrammarParserTotalFuelNonterminalSupport.v").write_text(
    r'''From Phil.Surface Require Export GrammarParserTotalFuelBase.
''')
(surface / "GrammarParserTotalFuelNonterminal.v").write_text(
    r'''From Phil.Surface Require Export GrammarParserTotalFuelNonterminalSupport.
''')

(surface / "GrammarParserTotalFuel.v").write_text(r'''From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyMutualPredictiveBridge
  GrammarDeterminacyPredictiveOracle
  GrammarParserProgress
  GrammarParserRecognizer.
From Phil.Surface Require Export GrammarParserTotalFuelValue.

Import ListNotations.

(*
  Public total-fuel facade for PHIL-SURFACE-GRAMMAR-CORR-001.

  GrammarParserTotalFuelValue.v carries the canonical proof.  It uses the same
  certified Grammar-v1 rank computation and the same total-fuel bound as the
  earlier raw-rank proof, but transports only the numeric rank value across the
  recursive induction boundary.  That representation closes quickly in Rocq
  9.2 and 9.3-rc1, whereas sealing the equivalent raw equality proof term is
  pathologically expensive.
*)

Theorem phase1_surface_predictive_parse_total_fuel_oracle_complete :
  forall tokens tree,
    OracleResolvedPhase1CompleteDerivation
      phase1_surface_predictive_oracle tokens tree ->
    phase1_surface_predictive_parse_fuel
      (phase1_surface_parser_total_fuel tokens) tokens =
      Some ([], ResultTree tree).
Proof.
  exact phase1_surface_predictive_parse_total_fuel_oracle_complete_value.
Qed.

Theorem phase1_surface_predictive_parse_total_fuel_complete :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    phase1_surface_predictive_parse_fuel
      (phase1_surface_parser_total_fuel tokens) tokens =
      Some ([], ResultTree tree).
Proof.
  exact phase1_surface_predictive_parse_total_fuel_complete_value.
Qed.

Theorem phase1_surface_predictive_total_fuel_accepts_iff_derivable :
  forall tokens,
    (exists tree,
      phase1_surface_predictive_parse_fuel
        (phase1_surface_parser_total_fuel tokens) tokens =
        Some ([], ResultTree tree)) <->
    (exists tree, Phase1CompleteDerivation tokens tree).
Proof.
  intros tokens.
  split.
  - intros [tree Hparse].
    exists tree.
    eapply phase1_surface_predictive_parse_fuel_ordinary_sound.
    exact Hparse.
  - intros [tree Hderive].
    exists tree.
    eapply phase1_surface_predictive_parse_total_fuel_complete_value.
    exact Hderive.
Qed.
''')