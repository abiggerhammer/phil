From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstUnaryExpressionSpine
  GrammarAstUnaryExpressionPostfixRefinedSpine
  GrammarAstUnaryExpressionRecursiveRefinedSpine
  GrammarAstPostfixExpressionRefinedSpine
  GrammarAstPostfixExpressionRecursiveGroupingSpine
  GrammarAstRecursiveGroupingTotality.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Replace the postfix leaf beneath arbitrary recursive unary negation with
   the recursive grouping postfix carrier. The legacy adapter recurses over
   the typed unary value, without fuel or a redundant copy of that value.

   The raw decoder consumes one unit of fuel per unary node and calls the
   existing computed-bound postfix decoder at its leaf. Its public entry
   computes a sufficient bound from the input tree. Named argument, command,
   and fallback boundaries remain those of the consumed postfix carrier. *)

Inductive Phase1SurfaceUnaryExpressionRecursiveGroupingSpine : Type :=
| Phase1UnaryGroupingNegate
    (operand : Phase1SurfaceUnaryExpressionRecursiveGroupingSpine)
| Phase1UnaryGroupingPostfix
    (postfix : Phase1SurfacePostfixExpressionRecursiveGroupingSpine).

Fixpoint phase1_surface_unary_expression_recursive_grouping_spine_tree
  (expression : Phase1SurfaceUnaryExpressionRecursiveGroupingSpine)
  : ParseTree :=
  match expression with
  | Phase1UnaryGroupingNegate operand =>
      PTNonterminal "unary_expression"
        (PTAlternative 0
          (PTSequence
            [ PTLiteral "-";
              phase1_surface_unary_expression_recursive_grouping_spine_tree
                operand ]))
  | Phase1UnaryGroupingPostfix postfix =>
      PTNonterminal "unary_expression"
        (PTAlternative 1
          (phase1_surface_postfix_expression_recursive_grouping_spine_tree
            postfix))
  end.

Fixpoint phase1_surface_refine_unary_expression_recursive_grouping
  (previous : Phase1SurfaceUnaryExpressionRecursiveRefinedSpine)
  : option Phase1SurfaceUnaryExpressionRecursiveGroupingSpine :=
  match previous with
  | Phase1SurfaceUnaryExpressionNegateRecursiveRefined operand =>
      option_map Phase1UnaryGroupingNegate
        (phase1_surface_refine_unary_expression_recursive_grouping operand)
  | Phase1SurfaceUnaryExpressionPostfixRecursiveRefined postfix =>
      option_map Phase1UnaryGroupingPostfix
        (phase1_surface_refine_postfix_expression_recursive_grouping postfix)
  end.

Theorem phase1_surface_refine_unary_expression_recursive_grouping_round_trip :
  forall previous expression,
    phase1_surface_refine_unary_expression_recursive_grouping previous =
      Some expression ->
    phase1_surface_unary_expression_recursive_grouping_spine_tree expression =
      phase1_surface_unary_expression_recursive_refined_spine_tree previous.
Proof.
  induction previous as [operand IH | postfix]; intros expression Hrefine.
  - cbn in Hrefine.
    destruct (phase1_surface_refine_unary_expression_recursive_grouping operand)
      as [refined |] eqn:Hoperand; try discriminate Hrefine.
    inversion Hrefine; subst expression.
    change
      (PTNonterminal "unary_expression"
        (PTAlternative 0
          (PTSequence [PTLiteral "-";
            phase1_surface_unary_expression_recursive_grouping_spine_tree
              refined])) =
       PTNonterminal "unary_expression"
        (PTAlternative 0
          (PTSequence [PTLiteral "-";
            phase1_surface_unary_expression_recursive_refined_spine_tree
              operand]))).
    rewrite (IH refined eq_refl). reflexivity.
  - cbn in Hrefine.
    destruct
      (phase1_surface_refine_postfix_expression_recursive_grouping postfix)
      as [refined |] eqn:Hpostfix; try discriminate Hrefine.
    inversion Hrefine; subst expression.
    change
      (PTNonterminal "unary_expression"
        (PTAlternative 1
          (phase1_surface_postfix_expression_recursive_grouping_spine_tree
            refined)) =
       PTNonterminal "unary_expression"
        (PTAlternative 1
          (phase1_surface_postfix_expression_refined_spine_tree postfix))).
    rewrite
      (phase1_surface_refine_postfix_expression_recursive_grouping_round_trip
        postfix refined Hpostfix).
    reflexivity.
Qed.

Fixpoint phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel
  (fuel : nat) (tree : ParseTree)
  : option Phase1SurfaceUnaryExpressionRecursiveGroupingSpine :=
  match fuel with
  | O => None
  | S remaining =>
      match phase1_surface_normalize_unary_expression_spine tree with
      | Some (Phase1SurfaceUnaryExpressionNegate operand) =>
          option_map Phase1UnaryGroupingNegate
            (phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel
              remaining operand)
      | Some (Phase1SurfaceUnaryExpressionPostfix postfix) =>
          option_map Phase1UnaryGroupingPostfix
            (phase1_surface_normalize_postfix_expression_recursive_grouping_tree
              postfix)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel_round_trip :
  forall fuel tree expression,
    phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel
      fuel tree = Some expression ->
    phase1_surface_unary_expression_recursive_grouping_spine_tree expression =
      tree.
Proof.
  induction fuel as [|fuel IH]; intros tree expression Hnormalize.
  - discriminate Hnormalize.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_unary_expression_spine tree)
      as [[operand | postfix] |] eqn:Hshell; try discriminate Hnormalize.
    + destruct
        (phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel
          fuel operand) as [refined |] eqn:Hoperand;
        try discriminate Hnormalize.
      inversion Hnormalize; subst expression.
      cbn [phase1_surface_unary_expression_recursive_grouping_spine_tree].
      rewrite (IH operand refined Hoperand).
      exact (phase1_surface_normalize_unary_expression_spine_round_trip
        tree (Phase1SurfaceUnaryExpressionNegate operand) Hshell).
    + destruct
        (phase1_surface_normalize_postfix_expression_recursive_grouping_tree
          postfix) as [refined |] eqn:Hpostfix;
        try discriminate Hnormalize.
      inversion Hnormalize; subst expression.
      cbn [phase1_surface_unary_expression_recursive_grouping_spine_tree].
      rewrite
        (phase1_surface_normalize_postfix_expression_recursive_grouping_tree_round_trip
          postfix refined Hpostfix).
      exact (phase1_surface_normalize_unary_expression_spine_round_trip
        tree (Phase1SurfaceUnaryExpressionPostfix postfix) Hshell).
Qed.

Definition phase1_surface_normalize_unary_expression_recursive_grouping_tree
  (tree : ParseTree)
  : option Phase1SurfaceUnaryExpressionRecursiveGroupingSpine :=
  phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel
    (phase1_surface_grouping_tree_size tree) tree.

Theorem phase1_surface_normalize_unary_expression_recursive_grouping_tree_round_trip :
  forall tree expression,
    phase1_surface_normalize_unary_expression_recursive_grouping_tree tree =
      Some expression ->
    phase1_surface_unary_expression_recursive_grouping_spine_tree expression =
      tree.
Proof.
  intros tree expression Hnormalize.
  eapply
    phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel_round_trip.
  exact Hnormalize.
Qed.
