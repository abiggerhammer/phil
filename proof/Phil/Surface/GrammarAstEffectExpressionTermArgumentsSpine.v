From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectExpressionSpine
  GrammarAstTermArgumentsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the reusable term_arguments spine into effect_expression.

  The already-refined static-reference label is preserved unchanged. Only the
  optional argument field advances from option ParseTree to
  option Phase1SurfaceTermArgumentsSpine.
*)

Definition phase1_surface_optional_term_arguments_spine_tree
  (arguments : option Phase1SurfaceTermArgumentsSpine) : ParseTree :=
  match arguments with
  | None => PTOptionalNone
  | Some arguments_value =>
      PTOptionalSome
        (phase1_surface_term_arguments_spine_tree arguments_value)
  end.

Definition phase1_surface_normalize_optional_term_arguments_spine
  (arguments : option ParseTree)
  : option (option Phase1SurfaceTermArgumentsSpine) :=
  match arguments with
  | None => Some None
  | Some arguments_tree =>
      match phase1_surface_normalize_term_arguments_spine arguments_tree with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_optional_term_arguments_spine_round_trip :
  forall arguments refined,
    phase1_surface_normalize_optional_term_arguments_spine arguments =
      Some refined ->
    phase1_surface_optional_term_arguments_spine_tree refined =
      phase1_surface_optional_term_arguments_tree arguments.
Proof.
  intros [arguments_tree |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_term_arguments_spine arguments_tree)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_term_arguments_spine_round_trip
        arguments_tree actual Harguments).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Record Phase1SurfaceEffectExpressionTermArgumentsSpine : Type := {
  phase1_effect_expression_term_arguments_spine_reference :
    Phase1SurfaceStaticReferenceSpine;
  phase1_effect_expression_term_arguments_spine_arguments :
    option Phase1SurfaceTermArgumentsSpine
}.

Definition phase1_surface_effect_expression_term_arguments_spine_tree
  (effect : Phase1SurfaceEffectExpressionTermArgumentsSpine) : ParseTree :=
  PTNonterminal "effect_expression"
    (PTSequence
      [ phase1_surface_static_reference_spine_tree
          (phase1_effect_expression_term_arguments_spine_reference effect);
        phase1_surface_optional_term_arguments_spine_tree
          (phase1_effect_expression_term_arguments_spine_arguments effect)
      ]).

Definition phase1_surface_normalize_effect_expression_term_arguments_spine
  (effect : Phase1SurfaceEffectExpressionSpine)
  : option Phase1SurfaceEffectExpressionTermArgumentsSpine :=
  match
    phase1_surface_normalize_optional_term_arguments_spine
      (phase1_effect_expression_spine_arguments effect)
  with
  | Some arguments =>
      Some
        {| phase1_effect_expression_term_arguments_spine_reference :=
             phase1_effect_expression_spine_reference effect;
           phase1_effect_expression_term_arguments_spine_arguments :=
             arguments |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_term_arguments_spine_round_trip :
  forall effect refined,
    phase1_surface_normalize_effect_expression_term_arguments_spine effect =
      Some refined ->
    phase1_surface_effect_expression_term_arguments_spine_tree refined =
      phase1_surface_effect_expression_spine_tree effect.
Proof.
  intros [reference arguments] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_term_arguments_spine arguments)
    as [actual |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_optional_term_arguments_spine_round_trip
      arguments actual Harguments).
  reflexivity.
Qed.

Definition phase1_surface_normalize_effect_expression_term_arguments_tree
  (tree : ParseTree)
  : option Phase1SurfaceEffectExpressionTermArgumentsSpine :=
  match phase1_surface_normalize_effect_expression_spine tree with
  | Some effect =>
      phase1_surface_normalize_effect_expression_term_arguments_spine effect
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_term_arguments_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_effect_expression_term_arguments_tree tree =
      Some refined ->
    phase1_surface_effect_expression_term_arguments_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_effect_expression_term_arguments_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_effect_expression_spine tree)
    as [effect |] eqn:Heffect; try discriminate Hnormalize.
  transitivity (phase1_surface_effect_expression_spine_tree effect).
  - eapply
      phase1_surface_normalize_effect_expression_term_arguments_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_effect_expression_spine_round_trip.
    exact Heffect.
Qed.
