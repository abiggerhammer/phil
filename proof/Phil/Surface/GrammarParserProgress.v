From Stdlib Require Import Arith.PeanoNat Lia Lists.List.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationLookahead
  GrammarDerivationOracle
  GrammarParserRank.

Import ListNotations.

(*
  Dynamic half of the finite parser measure for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  GrammarParserRank.v certifies the exact Grammar-v1 same-input recursion
  component.  This file proves the orthogonal runtime component: every
  oracle-resolved derivation consumes a prefix, hence any recursive parse that
  actually changes its input strictly decreases the remaining token count.

  The successor slice combines token-count descent with the certified
  same-input rank to obtain a uniform finite recognizer fuel bound.
*)

Theorem oracle_derivation_consumes_prefix :
  forall oracle rules goal input rest result,
    OracleDerives oracle rules goal input rest result ->
    exists consumed,
      input = List.app consumed rest.
Proof.
  intros oracle rules goal input rest result Hderive.
  pose proof
    (oracle_derivation_erases
      oracle rules goal input rest result Hderive) as Herase.
  destruct goal as
    [path expression | path index items | path body];
    destruct result as [tree | trees];
    simpl in Herase; try contradiction.
  - eapply derives_consumes_prefix.
    exact Herase.
  - eapply derives_sequence_consumes_prefix.
    exact Herase.
  - eapply derives_repetition_consumes_prefix.
    exact Herase.
Qed.

Corollary oracle_derivation_length_nonincreasing :
  forall oracle rules goal input rest result,
    OracleDerives oracle rules goal input rest result ->
    List.length rest <= List.length input.
Proof.
  intros oracle rules goal input rest result Hderive.
  destruct
    (oracle_derivation_consumes_prefix
      oracle rules goal input rest result Hderive)
    as [consumed Hprefix].
  rewrite Hprefix, List.length_app.
  lia.
Qed.

Lemma prefix_progress_decreases_length :
  forall (input rest : list ConcreteToken) consumed,
    input = List.app consumed rest ->
    input <> rest ->
    List.length rest < List.length input.
Proof.
  intros input rest consumed Hprefix Hprogress.
  destruct consumed as [| token consumed].
  - simpl in Hprefix.
    contradiction.
  - rewrite Hprefix, List.length_app.
    simpl.
    lia.
Qed.

Corollary oracle_derivation_progress_decreases_length :
  forall oracle rules goal input rest result,
    OracleDerives oracle rules goal input rest result ->
    input <> rest ->
    List.length rest < List.length input.
Proof.
  intros oracle rules goal input rest result Hderive Hprogress.
  destruct
    (oracle_derivation_consumes_prefix
      oracle rules goal input rest result Hderive)
    as [consumed Hprefix].
  eapply prefix_progress_decreases_length; eauto.
Qed.

Lemma prefix_same_length_is_exact :
  forall (input rest : list ConcreteToken) consumed,
    input = List.app consumed rest ->
    List.length input = List.length rest ->
    input = rest.
Proof.
  intros input rest consumed Hprefix Hlength.
  assert (Hconsumed : List.length consumed = 0).
  {
    rewrite Hprefix, List.length_app in Hlength.
    lia.
  }
  apply List.length_zero_iff_nil in Hconsumed.
  subst consumed.
  exact Hprefix.
Qed.

Corollary oracle_derivation_same_length_is_exact :
  forall oracle rules goal input rest result,
    OracleDerives oracle rules goal input rest result ->
    List.length input = List.length rest ->
    input = rest.
Proof.
  intros oracle rules goal input rest result Hderive Hlength.
  destruct
    (oracle_derivation_consumes_prefix
      oracle rules goal input rest result Hderive)
    as [consumed Hprefix].
  eapply prefix_same_length_is_exact; eauto.
Qed.

Definition phase1_surface_parser_total_fuel
  (tokens : list ConcreteToken) : nat :=
  S
    ((S (List.length tokens)) *
      phase1_surface_parser_max_goal_rank).

Theorem phase1_surface_parser_total_fuel_positive :
  forall tokens,
    0 < phase1_surface_parser_total_fuel tokens.
Proof.
  intros tokens.
  unfold phase1_surface_parser_total_fuel.
  lia.
Qed.

Theorem phase1_surface_parser_total_fuel_decreases_on_token_progress :
  forall input rest,
    List.length rest < List.length input ->
    phase1_surface_parser_total_fuel rest <
      phase1_surface_parser_total_fuel input.
Proof.
  intros input rest Hlength.
  unfold phase1_surface_parser_total_fuel,
    phase1_surface_parser_max_goal_rank.
  nia.
Qed.

Corollary oracle_derivation_decreases_total_fuel_on_progress :
  forall oracle rules goal input rest result,
    OracleDerives oracle rules goal input rest result ->
    input <> rest ->
    phase1_surface_parser_total_fuel rest <
      phase1_surface_parser_total_fuel input.
Proof.
  intros oracle rules goal input rest result Hderive Hprogress.
  apply phase1_surface_parser_total_fuel_decreases_on_token_progress.
  eapply oracle_derivation_progress_decreases_length; eauto.
Qed.
