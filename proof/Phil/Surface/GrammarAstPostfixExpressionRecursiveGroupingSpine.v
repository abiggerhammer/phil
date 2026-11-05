From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstNamedPostfixExpressionRefinedTailSpine
  GrammarAstPostfixExpressionNamedRefinedSpine
  GrammarAstPostfixExpressionRefinedSpine
  GrammarAstPrimaryExpressionIntegerSpine
  GrammarAstPrimaryExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Consume the recursive grouping primary carrier in the postfix-expression
  representation.  The primary field is replaced rather than accompanied by
  a second representation.  The named branch and primary projection names
  keep exactly their existing representations.

  Recursive tuple and parenthesized expression payloads are therefore exposed
  through the primary branch.  Named term arguments, static arguments, and the
  command/fallback boundaries of the recursive grouping carrier are unchanged.
  This slice does not lift the new postfix type through enclosing expression
  or declaration carriers, or establish Haskell parser correspondence.
*)

Inductive Phase1SurfacePostfixExpressionRecursiveGroupingSpine : Type :=
| Phase1PostfixGroupingNamed
    (named : Phase1SurfaceNamedPostfixExpressionRefinedTailSpine)
| Phase1PostfixGroupingPrimary
    (primary : Phase1SurfacePrimaryExpressionRecursiveGroupingSpine)
    (projections : list string).

Definition phase1_surface_postfix_expression_recursive_grouping_spine_tree
  (expression : Phase1SurfacePostfixExpressionRecursiveGroupingSpine)
  : ParseTree :=
  match expression with
  | Phase1PostfixGroupingNamed named =>
      phase1_surface_postfix_expression_named_refined_spine_tree
        (Phase1SurfacePostfixExpressionNamedRefined named)
  | Phase1PostfixGroupingPrimary primary projections =>
      phase1_surface_postfix_expression_named_refined_spine_tree
        (Phase1SurfacePostfixExpressionPrimaryRetained
          (phase1_surface_primary_expression_recursive_grouping_spine_tree
            primary)
          projections)
  end.

Definition phase1_surface_refine_postfix_expression_recursive_grouping
  (previous : Phase1SurfacePostfixExpressionRefinedSpine)
  : option Phase1SurfacePostfixExpressionRecursiveGroupingSpine :=
  match previous with
  | Phase1SurfacePostfixExpressionNamedFullyRefined named =>
      Some (Phase1PostfixGroupingNamed named)
  | Phase1SurfacePostfixExpressionPrimaryRefined primary projections =>
      match
        phase1_surface_refine_primary_expression_recursive_grouping primary
      with
      | Some refined =>
          Some (Phase1PostfixGroupingPrimary refined projections)
      | None => None
      end
  end.

Theorem phase1_surface_refine_postfix_expression_recursive_grouping_round_trip :
  forall previous expression,
    phase1_surface_refine_postfix_expression_recursive_grouping previous =
      Some expression ->
    phase1_surface_postfix_expression_recursive_grouping_spine_tree expression =
      phase1_surface_postfix_expression_refined_spine_tree previous.
Proof.
  intros previous expression Hrefine.
  destruct previous as [named | primary projections].
  - inversion Hrefine; subst expression.
    reflexivity.
  - unfold phase1_surface_refine_postfix_expression_recursive_grouping
      in Hrefine.
    destruct
      (phase1_surface_refine_primary_expression_recursive_grouping primary)
      as [refined |] eqn:Hprimary;
      try discriminate Hrefine.
    inversion Hrefine; subst expression.
    unfold phase1_surface_postfix_expression_recursive_grouping_spine_tree,
      phase1_surface_postfix_expression_refined_spine_tree.
    rewrite
      (phase1_surface_refine_primary_expression_recursive_grouping_round_trip
        primary refined Hprimary).
    reflexivity.
Qed.

Definition phase1_surface_normalize_postfix_expression_recursive_grouping_tree
  (tree : ParseTree)
  : option Phase1SurfacePostfixExpressionRecursiveGroupingSpine :=
  match phase1_surface_normalize_postfix_expression_refined_tree tree with
  | Some previous =>
      phase1_surface_refine_postfix_expression_recursive_grouping previous
  | None => None
  end.

Theorem
  phase1_surface_normalize_postfix_expression_recursive_grouping_tree_round_trip :
  forall tree expression,
    phase1_surface_normalize_postfix_expression_recursive_grouping_tree tree =
      Some expression ->
    phase1_surface_postfix_expression_recursive_grouping_spine_tree expression =
      tree.
Proof.
  intros tree expression Hnormalize.
  unfold phase1_surface_normalize_postfix_expression_recursive_grouping_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_postfix_expression_refined_tree tree)
    as [previous |] eqn:Hprevious;
    try discriminate Hnormalize.
  transitivity (phase1_surface_postfix_expression_refined_spine_tree previous).
  - eapply
      phase1_surface_refine_postfix_expression_recursive_grouping_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_postfix_expression_refined_tree_round_trip.
    exact Hprevious.
Qed.
