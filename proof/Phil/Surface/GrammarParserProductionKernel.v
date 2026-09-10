From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarDerivationOracle
  GrammarParserProgress
  GrammarParserRecognizer.

Import ListNotations.

(*
  Executable production-facing wrapper for PHIL-SURFACE-GRAMMAR-CORR-001.

  #830 proved that the predictive reference recognizer, run with
  phase1_surface_parser_total_fuel, accepts exactly the complete Grammar-v1
  derivations.  This file does not introduce a second parser or a second fuel
  formula: it names that exact executable composition for extraction and later
  production binding.
*)

Definition phase1_surface_reference_parse
  (tokens : list ConcreteToken)
  : option (list ConcreteToken * DerivationResult) :=
  phase1_surface_predictive_parse_fuel
    (phase1_surface_parser_total_fuel tokens)
    tokens.

Definition phase1_surface_reference_accepts
  (tokens : list ConcreteToken) : bool :=
  match phase1_surface_reference_parse tokens with
  | Some ([], ResultTree _) => true
  | _ => false
  end.
