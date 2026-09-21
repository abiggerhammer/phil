From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetTermArgumentsSpine
  GrammarAstEffectExpressionExpressionOuterSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the expression-outer-refined effect_expression carrier through
  effect-set literals and the enclosing effect_set_expression choice.

  Literal member order and punctuation remain exact. The static-reference
  branch is unchanged.
*)

Fixpoint phase1_surface_normalize_effect_expression_expression_outer_values
  (effects : list Phase1SurfaceEffectExpressionTermArgumentsSpine)
  : option (list Phase1SurfaceEffectExpressionExpressionOuterSpine) :=
  match effects with
  | [] => Some []
  | effect :: rest =>
      match
        phase1_surface_normalize_effect_expression_expression_outer_spine effect,
        phase1_surface_normalize_effect_expression_expression_outer_values rest
      with
      | Some refined, Some refined_rest =>
          Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_outer_values_round_trip :
  forall effects refined,
    phase1_surface_normalize_effect_expression_expression_outer_values effects =
      Some refined ->
    map phase1_surface_effect_expression_expression_outer_spine_tree refined =
      map phase1_surface_effect_expression_term_arguments_spine_tree effects.
Proof.
  intros effects.
  induction effects as [|effect rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_expression_outer_spine effect)
      as [actual |] eqn:Heffect; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_expression_outer_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_effect_expression_expression_outer_spine_round_trip.
      exact Heffect.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_effect_expression_expression_outer_suffix_tree
  (effect : Phase1SurfaceEffectExpressionExpressionOuterSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_effect_expression_expression_outer_spine_tree effect
    ].

Definition phase1_surface_effect_expression_expression_outer_entries_tree
  (effects : list Phase1SurfaceEffectExpressionExpressionOuterSpine) : ParseTree :=
  match effects with
  | [] => PTOptionalNone
  | first :: rest =>
      PTOptionalSome
        (PTSequence
          [ phase1_surface_effect_expression_expression_outer_spine_tree first;
            PTRepetition
              (map
                phase1_surface_effect_expression_expression_outer_suffix_tree
                rest)
          ])
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_outer_values_entries_round_trip :
  forall effects refined,
    phase1_surface_normalize_effect_expression_expression_outer_values effects =
      Some refined ->
    phase1_surface_effect_expression_expression_outer_entries_tree refined =
      phase1_surface_effect_expression_term_arguments_entries_tree effects.
Proof.
  intros effects.
  induction effects as [|effect rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_expression_outer_spine effect)
      as [actual |] eqn:Heffect; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_effect_expression_expression_outer_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effect_expression_expression_outer_spine_round_trip
        effect actual Heffect).
    pose proof
      (phase1_surface_normalize_effect_expression_expression_outer_values_round_trip
        rest actual_rest Hrest) as Hrest_round_trip.
    unfold phase1_surface_effect_expression_expression_outer_suffix_tree.
    unfold phase1_surface_effect_expression_term_arguments_suffix_tree.
    cbn in Hrest_round_trip |- *.
    rewrite Hrest_round_trip.
    reflexivity.
Qed.

Record Phase1SurfaceEffectSetExpressionOuterLiteralSpine : Type := {
  phase1_effect_set_expression_outer_literal_spine_effects :
    list Phase1SurfaceEffectExpressionExpressionOuterSpine
}.

Definition phase1_surface_effect_set_expression_outer_literal_spine_tree
  (literal : Phase1SurfaceEffectSetExpressionOuterLiteralSpine) : ParseTree :=
  PTNonterminal "effect_set_literal"
    (PTSequence
      [ PTLiteral "{";
        phase1_surface_effect_expression_expression_outer_entries_tree
          (phase1_effect_set_expression_outer_literal_spine_effects literal);
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_effect_set_expression_outer_literal_spine
  (literal : Phase1SurfaceEffectSetTermArgumentsLiteralSpine)
  : option Phase1SurfaceEffectSetExpressionOuterLiteralSpine :=
  match
    phase1_surface_normalize_effect_expression_expression_outer_values
      (phase1_effect_set_term_arguments_literal_spine_effects literal)
  with
  | Some effects =>
      Some
        {| phase1_effect_set_expression_outer_literal_spine_effects := effects |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_set_expression_outer_literal_spine_round_trip :
  forall literal refined,
    phase1_surface_normalize_effect_set_expression_outer_literal_spine literal =
      Some refined ->
    phase1_surface_effect_set_expression_outer_literal_spine_tree refined =
      phase1_surface_effect_set_term_arguments_literal_spine_tree literal.
Proof.
  intros [effects] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_effect_expression_expression_outer_values effects)
    as [actual |] eqn:Heffects; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_effect_expression_expression_outer_values_entries_round_trip
      effects actual Heffects).
  reflexivity.
Qed.

Inductive Phase1SurfaceEffectSetExpressionOuterSpine : Type :=
| Phase1EffectSetExpressionOuterLiteral
    (literal : Phase1SurfaceEffectSetExpressionOuterLiteralSpine)
| Phase1EffectSetExpressionOuterReference
    (reference : Phase1SurfaceStaticReferenceSpine).

Definition phase1_surface_effect_set_expression_outer_spine_tree
  (effects : Phase1SurfaceEffectSetExpressionOuterSpine) : ParseTree :=
  match effects with
  | Phase1EffectSetExpressionOuterLiteral literal =>
      PTNonterminal "effect_set_expression"
        (PTAlternative 0
          (phase1_surface_effect_set_expression_outer_literal_spine_tree literal))
  | Phase1EffectSetExpressionOuterReference reference =>
      PTNonterminal "effect_set_expression"
        (PTAlternative 1
          (phase1_surface_static_reference_spine_tree reference))
  end.

Definition phase1_surface_normalize_effect_set_expression_outer_spine
  (effects : Phase1SurfaceEffectSetTermArgumentsSpine)
  : option Phase1SurfaceEffectSetExpressionOuterSpine :=
  match effects with
  | Phase1EffectSetTermArgumentsLiteral literal =>
      match
        phase1_surface_normalize_effect_set_expression_outer_literal_spine literal
      with
      | Some refined =>
          Some (Phase1EffectSetExpressionOuterLiteral refined)
      | None => None
      end
  | Phase1EffectSetTermArgumentsReference reference =>
      Some (Phase1EffectSetExpressionOuterReference reference)
  end.

Theorem
  phase1_surface_normalize_effect_set_expression_outer_spine_round_trip :
  forall effects refined,
    phase1_surface_normalize_effect_set_expression_outer_spine effects =
      Some refined ->
    phase1_surface_effect_set_expression_outer_spine_tree refined =
      phase1_surface_effect_set_term_arguments_spine_tree effects.
Proof.
  intros effects refined Hnormalize.
  destruct effects as [literal | reference].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_effect_set_expression_outer_literal_spine literal)
      as [actual |] eqn:Hliteral; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effect_set_expression_outer_literal_spine_round_trip
        literal actual Hliteral).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_effect_set_expression_outer_tree
  (tree : ParseTree)
  : option Phase1SurfaceEffectSetExpressionOuterSpine :=
  match phase1_surface_normalize_effect_set_term_arguments_tree tree with
  | Some effects =>
      phase1_surface_normalize_effect_set_expression_outer_spine effects
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_set_expression_outer_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_effect_set_expression_outer_tree tree =
      Some refined ->
    phase1_surface_effect_set_expression_outer_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_effect_set_expression_outer_tree in Hnormalize.
  destruct
    (phase1_surface_normalize_effect_set_term_arguments_tree tree)
    as [effects |] eqn:Heffects; try discriminate Hnormalize.
  transitivity (phase1_surface_effect_set_term_arguments_spine_tree effects).
  - eapply
      phase1_surface_normalize_effect_set_expression_outer_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_effect_set_term_arguments_tree_round_trip.
    exact Heffects.
Qed.
