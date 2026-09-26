From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixExpressionSpine
  GrammarAstNamedPostfixTermProjectionSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the fully refined present named-postfix tail back into the enclosing
  named_postfix_expression carrier.

  The qualified-name prefix was already refined by
  GrammarAstNamedPostfixExpressionSpine.  The present-tail alternatives are
  now fully refined through static/term arguments and repeated projections.
  This focused slice replaces only the retained optional ParseTree tail with
  an optional semantic tail carrier.
*)

Record Phase1SurfaceNamedPostfixExpressionRefinedTailSpine : Type := {
  phase1_named_postfix_expression_refined_tail_name : Phase1SurfaceNameList;
  phase1_named_postfix_expression_refined_tail :
    option Phase1SurfaceNamedPostfixTermProjectionSpine
}.

Definition phase1_surface_named_postfix_expression_refined_tail_tree
  (tail : option Phase1SurfaceNamedPostfixTermProjectionSpine) : ParseTree :=
  match tail with
  | None => PTOptionalNone
  | Some tail_value =>
      PTOptionalSome
        (phase1_surface_named_postfix_term_projection_spine_tree tail_value)
  end.

Definition phase1_surface_named_postfix_expression_refined_tail_spine_tree
  (expression : Phase1SurfaceNamedPostfixExpressionRefinedTailSpine)
  : ParseTree :=
  PTNonterminal "named_postfix_expression"
    (PTSequence
      [ phase1_surface_qualified_name_tree
          (phase1_named_postfix_expression_refined_tail_name expression);
        phase1_surface_named_postfix_expression_refined_tail_tree
          (phase1_named_postfix_expression_refined_tail expression)
      ]).

Definition phase1_surface_normalize_named_postfix_expression_refined_tail
  (tail : option ParseTree)
  : option (option Phase1SurfaceNamedPostfixTermProjectionSpine) :=
  match tail with
  | None => Some None
  | Some tail_tree =>
      match phase1_surface_normalize_named_postfix_term_projection_tree tail_tree with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Lemma
  phase1_surface_normalize_named_postfix_expression_refined_tail_round_trip :
  forall tail refined,
    phase1_surface_normalize_named_postfix_expression_refined_tail tail =
      Some refined ->
    phase1_surface_named_postfix_expression_refined_tail_tree refined =
      phase1_surface_named_postfix_expression_tail_tree tail.
Proof.
  intros tail refined Hnormalize.
  destruct tail as [tail_tree |].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_named_postfix_term_projection_tree tail_tree)
      as [tail_value |] eqn:Htail; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_named_postfix_term_projection_tree_round_trip
        tail_tree tail_value Htail).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_named_postfix_expression_refined_tail_spine
  (expression : Phase1SurfaceNamedPostfixExpressionSpine)
  : option Phase1SurfaceNamedPostfixExpressionRefinedTailSpine :=
  match
    phase1_surface_normalize_named_postfix_expression_refined_tail
      (phase1_named_postfix_expression_spine_tail expression)
  with
  | Some tail =>
      Some
        {| phase1_named_postfix_expression_refined_tail_name :=
             phase1_named_postfix_expression_spine_name expression;
           phase1_named_postfix_expression_refined_tail := tail |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_named_postfix_expression_refined_tail_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_named_postfix_expression_refined_tail_spine
      expression = Some refined ->
    phase1_surface_named_postfix_expression_refined_tail_spine_tree refined =
      phase1_surface_named_postfix_expression_spine_tree expression.
Proof.
  intros expression refined Hnormalize.
  destruct expression as [name tail].
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_named_postfix_expression_refined_tail tail)
    as [tail_value |] eqn:Htail; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_named_postfix_expression_refined_tail_round_trip
      tail tail_value Htail).
  reflexivity.
Qed.

Definition phase1_surface_normalize_named_postfix_expression_refined_tail_tree
  (tree : ParseTree)
  : option Phase1SurfaceNamedPostfixExpressionRefinedTailSpine :=
  match phase1_surface_normalize_named_postfix_expression_spine tree with
  | Some expression =>
      phase1_surface_normalize_named_postfix_expression_refined_tail_spine
        expression
  | None => None
  end.

Theorem
  phase1_surface_normalize_named_postfix_expression_refined_tail_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_named_postfix_expression_refined_tail_tree tree =
      Some refined ->
    phase1_surface_named_postfix_expression_refined_tail_spine_tree refined =
      tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_named_postfix_expression_refined_tail_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_named_postfix_expression_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  transitivity
    (phase1_surface_named_postfix_expression_spine_tree expression).
  - eapply
      phase1_surface_normalize_named_postfix_expression_refined_tail_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_named_postfix_expression_spine_round_trip.
    exact Hexpression.
Qed.
