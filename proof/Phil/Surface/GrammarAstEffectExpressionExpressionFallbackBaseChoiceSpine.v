From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectExpressionExpressionOuterSpine
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the fallback/base-choice-refined term_arguments carrier into
  effect_expression.

  The already-refined static-reference label remains unchanged. Only a present
  term-arguments value advances from Phase1SurfaceTermArgumentsExpressionOuterSpine
  to Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine.
*)

Definition
  phase1_surface_optional_term_arguments_expression_fallback_base_choice_tree
  (arguments : option Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine)
  : ParseTree :=
  match arguments with
  | None => PTOptionalNone
  | Some arguments_value =>
      PTOptionalSome
        (phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
          arguments_value)
  end.

Definition
  phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice
  (arguments : option Phase1SurfaceTermArgumentsExpressionOuterSpine)
  : option (option Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine) :=
  match arguments with
  | None => Some None
  | Some arguments_value =>
      match
        phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine
          arguments_value
      with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_round_trip :
  forall arguments refined,
    phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice
      arguments = Some refined ->
    phase1_surface_optional_term_arguments_expression_fallback_base_choice_tree
      refined =
      phase1_surface_optional_term_arguments_expression_outer_tree arguments.
Proof.
  intros [arguments_value |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine
        arguments_value)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine_round_trip
        arguments_value actual Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Record Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceSpine : Type := {
  phase1_effect_expression_expression_fallback_base_choice_spine_reference :
    Phase1SurfaceStaticReferenceSpine;
  phase1_effect_expression_expression_fallback_base_choice_spine_arguments :
    option Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceSpine
}.

Definition phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
  (effect : Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceSpine)
  : ParseTree :=
  PTNonterminal "effect_expression"
    (PTSequence
      [ phase1_surface_static_reference_spine_tree
          (phase1_effect_expression_expression_fallback_base_choice_spine_reference
            effect);
        phase1_surface_optional_term_arguments_expression_fallback_base_choice_tree
          (phase1_effect_expression_expression_fallback_base_choice_spine_arguments
            effect)
      ]).

Definition
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_spine
  (effect : Phase1SurfaceEffectExpressionExpressionOuterSpine)
  : option Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceSpine :=
  match
    phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice
      (phase1_effect_expression_expression_outer_spine_arguments effect)
  with
  | Some arguments =>
      Some
        {| phase1_effect_expression_expression_fallback_base_choice_spine_reference :=
             phase1_effect_expression_expression_outer_spine_reference effect;
           phase1_effect_expression_expression_fallback_base_choice_spine_arguments :=
             arguments |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_spine_round_trip :
  forall effect refined,
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_spine
      effect = Some refined ->
    phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
      refined =
      phase1_surface_effect_expression_expression_outer_spine_tree effect.
Proof.
  intros [reference arguments] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice
      arguments)
    as [actual |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_round_trip
      arguments actual Harguments).
  reflexivity.
Qed.

Definition
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree
  (tree : ParseTree)
  : option Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceSpine :=
  match phase1_surface_normalize_effect_expression_expression_outer_tree tree with
  | Some effect =>
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_spine
        effect
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree
      tree = Some refined ->
    phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
      refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_effect_expression_expression_outer_tree tree)
    as [effect |] eqn:Heffect; try discriminate Hnormalize.
  transitivity
    (phase1_surface_effect_expression_expression_outer_spine_tree effect).
  - eapply
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_spine_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_effect_expression_expression_outer_tree_round_trip.
    exact Heffect.
Qed.
