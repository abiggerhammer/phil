From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectExpressionTermArgumentsSpine
  GrammarAstTermArgumentsExpressionOuterSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the expression-outer-refined term_arguments carrier into effect_expression.

  The already-refined static-reference label remains unchanged. Only a present
  term-arguments value advances from Phase1SurfaceTermArgumentsSpine to
  Phase1SurfaceTermArgumentsExpressionOuterSpine.
*)

Definition phase1_surface_optional_term_arguments_expression_outer_tree
  (arguments : option Phase1SurfaceTermArgumentsExpressionOuterSpine)
  : ParseTree :=
  match arguments with
  | None => PTOptionalNone
  | Some arguments_value =>
      PTOptionalSome
        (phase1_surface_term_arguments_expression_outer_spine_tree
          arguments_value)
  end.

Definition phase1_surface_normalize_optional_term_arguments_expression_outer
  (arguments : option Phase1SurfaceTermArgumentsSpine)
  : option (option Phase1SurfaceTermArgumentsExpressionOuterSpine) :=
  match arguments with
  | None => Some None
  | Some arguments_value =>
      match
        phase1_surface_normalize_term_arguments_expression_outer_spine
          arguments_value
      with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_term_arguments_expression_outer_round_trip :
  forall arguments refined,
    phase1_surface_normalize_optional_term_arguments_expression_outer arguments =
      Some refined ->
    phase1_surface_optional_term_arguments_expression_outer_tree refined =
      phase1_surface_optional_term_arguments_spine_tree arguments.
Proof.
  intros [arguments_value |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_term_arguments_expression_outer_spine
        arguments_value)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_term_arguments_expression_outer_spine_round_trip
        arguments_value actual Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Record Phase1SurfaceEffectExpressionExpressionOuterSpine : Type := {
  phase1_effect_expression_expression_outer_spine_reference :
    Phase1SurfaceStaticReferenceSpine;
  phase1_effect_expression_expression_outer_spine_arguments :
    option Phase1SurfaceTermArgumentsExpressionOuterSpine
}.

Definition phase1_surface_effect_expression_expression_outer_spine_tree
  (effect : Phase1SurfaceEffectExpressionExpressionOuterSpine) : ParseTree :=
  PTNonterminal "effect_expression"
    (PTSequence
      [ phase1_surface_static_reference_spine_tree
          (phase1_effect_expression_expression_outer_spine_reference effect);
        phase1_surface_optional_term_arguments_expression_outer_tree
          (phase1_effect_expression_expression_outer_spine_arguments effect)
      ]).

Definition phase1_surface_normalize_effect_expression_expression_outer_spine
  (effect : Phase1SurfaceEffectExpressionTermArgumentsSpine)
  : option Phase1SurfaceEffectExpressionExpressionOuterSpine :=
  match
    phase1_surface_normalize_optional_term_arguments_expression_outer
      (phase1_effect_expression_term_arguments_spine_arguments effect)
  with
  | Some arguments =>
      Some
        {| phase1_effect_expression_expression_outer_spine_reference :=
             phase1_effect_expression_term_arguments_spine_reference effect;
           phase1_effect_expression_expression_outer_spine_arguments :=
             arguments |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_outer_spine_round_trip :
  forall effect refined,
    phase1_surface_normalize_effect_expression_expression_outer_spine effect =
      Some refined ->
    phase1_surface_effect_expression_expression_outer_spine_tree refined =
      phase1_surface_effect_expression_term_arguments_spine_tree effect.
Proof.
  intros [reference arguments] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_term_arguments_expression_outer arguments)
    as [actual |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_term_arguments_expression_outer_round_trip
      arguments actual Harguments).
  reflexivity.
Qed.

Definition phase1_surface_normalize_effect_expression_expression_outer_tree
  (tree : ParseTree)
  : option Phase1SurfaceEffectExpressionExpressionOuterSpine :=
  match
    phase1_surface_normalize_effect_expression_term_arguments_tree tree
  with
  | Some effect =>
      phase1_surface_normalize_effect_expression_expression_outer_spine effect
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_outer_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_effect_expression_expression_outer_tree tree =
      Some refined ->
    phase1_surface_effect_expression_expression_outer_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_effect_expression_expression_outer_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_effect_expression_term_arguments_tree tree)
    as [effect |] eqn:Heffect; try discriminate Hnormalize.
  transitivity
    (phase1_surface_effect_expression_term_arguments_spine_tree effect).
  - eapply
      phase1_surface_normalize_effect_expression_expression_outer_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_effect_expression_term_arguments_tree_round_trip.
    exact Heffect.
Qed.
