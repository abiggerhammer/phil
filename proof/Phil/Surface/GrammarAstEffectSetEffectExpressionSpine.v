From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectExpressionSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the refined effect_expression carrier through effect-set literals and the
  enclosing effect_set_expression choice.

  Literal member order and punctuation remain exact. The static-reference branch
  is unchanged.
*)

Fixpoint phase1_surface_normalize_effect_expression_values
  (effects : list ParseTree)
  : option (list Phase1SurfaceEffectExpressionSpine) :=
  match effects with
  | [] => Some []
  | effect :: rest =>
      match phase1_surface_normalize_effect_expression_spine effect,
            phase1_surface_normalize_effect_expression_values rest with
      | Some refined, Some refined_rest =>
          Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_effect_expression_values_round_trip :
  forall effects refined,
    phase1_surface_normalize_effect_expression_values effects = Some refined ->
    map phase1_surface_effect_expression_spine_tree refined = effects.
Proof.
  intros effects.
  induction effects as [|effect rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_effect_expression_spine effect)
      as [actual |] eqn:Heffect; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_effect_expression_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_effect_expression_spine_round_trip.
      exact Heffect.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_effect_expression_refined_suffix_tree
  (effect : Phase1SurfaceEffectExpressionSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_effect_expression_spine_tree effect
    ].

Definition phase1_surface_effect_expression_refined_entries_tree
  (effects : list Phase1SurfaceEffectExpressionSpine) : ParseTree :=
  match effects with
  | [] => PTOptionalNone
  | first :: rest =>
      PTOptionalSome
        (PTSequence
          [ phase1_surface_effect_expression_spine_tree first;
            PTRepetition
              (map phase1_surface_effect_expression_refined_suffix_tree rest)
          ])
  end.

Theorem phase1_surface_normalize_effect_expression_values_entries_round_trip :
  forall effects refined,
    phase1_surface_normalize_effect_expression_values effects = Some refined ->
    phase1_surface_effect_expression_refined_entries_tree refined =
      phase1_surface_effect_set_entries_tree effects.
Proof.
  intros effects.
  induction effects as [|effect rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_effect_expression_spine effect)
      as [actual |] eqn:Heffect; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_effect_expression_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effect_expression_spine_round_trip
        effect actual Heffect).
    pose proof
      (phase1_surface_normalize_effect_expression_values_round_trip
        rest actual_rest Hrest) as Hrest_round_trip.
    unfold phase1_surface_effect_expression_refined_suffix_tree.
    unfold phase1_surface_effect_set_suffix_tree.
    cbn in Hrest_round_trip |- *.
    rewrite Hrest_round_trip.
    reflexivity.
Qed.

Record Phase1SurfaceEffectSetEffectExpressionLiteralSpine : Type := {
  phase1_effect_set_effect_expression_literal_spine_effects :
    list Phase1SurfaceEffectExpressionSpine
}.

Definition phase1_surface_effect_set_effect_expression_literal_spine_tree
  (literal : Phase1SurfaceEffectSetEffectExpressionLiteralSpine) : ParseTree :=
  PTNonterminal "effect_set_literal"
    (PTSequence
      [ PTLiteral "{";
        phase1_surface_effect_expression_refined_entries_tree
          (phase1_effect_set_effect_expression_literal_spine_effects literal);
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_effect_set_effect_expression_literal_spine
  (literal : Phase1SurfaceEffectSetLiteralSpine)
  : option Phase1SurfaceEffectSetEffectExpressionLiteralSpine :=
  match
    phase1_surface_normalize_effect_expression_values
      (phase1_effect_set_literal_spine_effects literal)
  with
  | Some effects =>
      Some
        {| phase1_effect_set_effect_expression_literal_spine_effects :=
             effects |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_set_effect_expression_literal_spine_round_trip :
  forall literal refined,
    phase1_surface_normalize_effect_set_effect_expression_literal_spine
      literal = Some refined ->
    phase1_surface_effect_set_effect_expression_literal_spine_tree refined =
      phase1_surface_effect_set_literal_spine_tree literal.
Proof.
  intros [effects] refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_effect_expression_values effects)
    as [actual |] eqn:Heffects; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_effect_expression_values_entries_round_trip
      effects actual Heffects).
  reflexivity.
Qed.

Inductive Phase1SurfaceEffectSetEffectExpressionSpine : Type :=
| Phase1EffectSetEffectExpressionLiteral
    (literal : Phase1SurfaceEffectSetEffectExpressionLiteralSpine)
| Phase1EffectSetEffectExpressionReference
    (reference : Phase1SurfaceStaticReferenceSpine).

Definition phase1_surface_effect_set_effect_expression_spine_tree
  (effects : Phase1SurfaceEffectSetEffectExpressionSpine) : ParseTree :=
  match effects with
  | Phase1EffectSetEffectExpressionLiteral literal =>
      PTNonterminal "effect_set_expression"
        (PTAlternative 0
          (phase1_surface_effect_set_effect_expression_literal_spine_tree
            literal))
  | Phase1EffectSetEffectExpressionReference reference =>
      PTNonterminal "effect_set_expression"
        (PTAlternative 1
          (phase1_surface_static_reference_spine_tree reference))
  end.

Definition phase1_surface_normalize_effect_set_effect_expression_spine
  (effects : Phase1SurfaceEffectSetSpine)
  : option Phase1SurfaceEffectSetEffectExpressionSpine :=
  match effects with
  | Phase1EffectSetLiteral literal =>
      match
        phase1_surface_normalize_effect_set_effect_expression_literal_spine
          literal
      with
      | Some refined =>
          Some (Phase1EffectSetEffectExpressionLiteral refined)
      | None => None
      end
  | Phase1EffectSetReference reference =>
      Some (Phase1EffectSetEffectExpressionReference reference)
  end.

Theorem phase1_surface_normalize_effect_set_effect_expression_spine_round_trip :
  forall effects refined,
    phase1_surface_normalize_effect_set_effect_expression_spine effects =
      Some refined ->
    phase1_surface_effect_set_effect_expression_spine_tree refined =
      phase1_surface_effect_set_spine_tree effects.
Proof.
  intros effects refined Hnormalize.
  destruct effects as [literal | reference].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_effect_set_effect_expression_literal_spine
        literal)
      as [actual |] eqn:Hliteral; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_effect_set_effect_expression_literal_spine_round_trip
        literal actual Hliteral).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_effect_set_effect_expression_tree
  (tree : ParseTree)
  : option Phase1SurfaceEffectSetEffectExpressionSpine :=
  match phase1_surface_normalize_effect_set_spine tree with
  | Some effects =>
      phase1_surface_normalize_effect_set_effect_expression_spine effects
  | None => None
  end.

Theorem phase1_surface_normalize_effect_set_effect_expression_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_effect_set_effect_expression_tree tree =
      Some refined ->
    phase1_surface_effect_set_effect_expression_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_effect_set_effect_expression_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_effect_set_spine tree)
    as [effects |] eqn:Heffects; try discriminate Hnormalize.
  transitivity (phase1_surface_effect_set_spine_tree effects).
  - eapply
      phase1_surface_normalize_effect_set_effect_expression_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_effect_set_spine_round_trip.
    exact Heffects.
Qed.
