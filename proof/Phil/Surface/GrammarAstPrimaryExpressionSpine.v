From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPostfixExpressionNamedRefinedSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Open the primary-expression boundary retained by the postfix-expression
  refinement chain:

    primary_expression =
        tuple_expression
      | parenthesized_expression
      | "true"
      | "false"
      | "unit"
      | char_literal
      | runtime_string_literal
      | float_literal
      | integer_literal
      ;

  This focused slice exposes the exact outer alternative and retains the
  selected payload tree. The branch validator checks the exact grammar shape;
  tuple/grouping and lexical payloads remain exact certified ParseTree values
  for dedicated successor refinements.
*)

Definition phase1_surface_primary_expression_branch_valid
  (index : nat) (selected : ParseTree) : option unit :=
  match index with
  | 0 => phase1_surface_validate_named_node "tuple_expression" selected
  | 1 =>
      phase1_surface_validate_named_node "parenthesized_expression" selected
  | 2 => phase1_surface_expect_literal "true" selected
  | 3 => phase1_surface_expect_literal "false" selected
  | 4 => phase1_surface_expect_literal "unit" selected
  | 5 => phase1_surface_validate_named_node "char_literal" selected
  | 6 =>
      phase1_surface_validate_named_node "runtime_string_literal" selected
  | 7 => phase1_surface_validate_named_node "float_literal" selected
  | 8 => phase1_surface_validate_named_node "integer_literal" selected
  | _ => None
  end.

Record Phase1SurfacePrimaryExpressionSpine : Type := {
  phase1_primary_expression_spine_branch : nat;
  phase1_primary_expression_spine_selected : ParseTree
}.

Definition phase1_surface_primary_expression_spine_tree
  (expression : Phase1SurfacePrimaryExpressionSpine) : ParseTree :=
  PTNonterminal "primary_expression"
    (PTAlternative
      (phase1_primary_expression_spine_branch expression)
      (phase1_primary_expression_spine_selected expression)).

Definition phase1_surface_normalize_primary_expression_spine
  (tree : ParseTree) : option Phase1SurfacePrimaryExpressionSpine :=
  match phase1_surface_expect_nonterminal "primary_expression" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (index, selected) =>
          match
            phase1_surface_primary_expression_branch_valid index selected
          with
          | Some tt =>
              Some
                {| phase1_primary_expression_spine_branch := index;
                   phase1_primary_expression_spine_selected := selected |}
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_primary_expression_spine_round_trip :
  forall tree expression,
    phase1_surface_normalize_primary_expression_spine tree =
      Some expression ->
    phase1_surface_primary_expression_spine_tree expression = tree.
Proof.
  intros tree expression Hnormalize.
  unfold phase1_surface_normalize_primary_expression_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "primary_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct
    (phase1_surface_primary_expression_branch_valid index selected)
    as [[] |] eqn:Hbranch; try discriminate Hnormalize.
  inversion Hnormalize; subst expression.
  unfold phase1_surface_primary_expression_spine_tree.
  cbn.
  rewrite
    (phase1_surface_expect_nonterminal_round_trip
      "primary_expression" tree body Hnode).
  rewrite
    (phase1_surface_expect_alternative_round_trip
      body index selected Halternative).
  reflexivity.
Qed.
