From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyPredictiveFallbackSoundness.

(*
  Semantic bridge for the finite Grammar-v1 parser measure.

  GrammarParserGoalRank.v gives sequence-tail rank descent when the head is
  computed nullable.  A derivation that leaves its input unchanged must
  therefore be connected back to the computed nullable fixed point.  The
  determinacy proof already established the contrapositive: a safe expression
  computed nonnullable must consume input.  These lemmas expose the exact form
  needed by the total-fuel proof without reopening nullable witness soundness.
*)

Theorem phase1_surface_zero_consume_derivation_is_nullable :
  forall path expression input tree,
    Derives phase1_surface_rules path expression input input tree ->
    choice_bodies_nonnullable_fuel expression_fuel expression = true ->
    nullable_expression phase1_surface_nullable_facts expression = true.
Proof.
  intros path expression input tree Hderive Hsafe.
  destruct
    (nullable_expression phase1_surface_nullable_facts expression)
    eqn:Hnullable.
  - reflexivity.
  - exfalso.
    pose proof
      (phase1_surface_nonnullable_derivation_makes_progress
        path expression input input tree
        Hderive Hsafe Hnullable) as Hprogress.
    apply Hprogress.
    reflexivity.
Qed.

Corollary phase1_surface_zero_consume_oracle_expression_is_nullable :
  forall oracle path expression input tree,
    OracleDerives oracle phase1_surface_rules
      (GoalExpression path expression)
      input input (ResultTree tree) ->
    choice_bodies_nonnullable_fuel expression_fuel expression = true ->
    nullable_expression phase1_surface_nullable_facts expression = true.
Proof.
  intros oracle path expression input tree Hderive Hsafe.
  eapply phase1_surface_zero_consume_derivation_is_nullable.
  - eapply oracle_resolved_expression_erases.
    exact Hderive.
  - exact Hsafe.
Qed.
