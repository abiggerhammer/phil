From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingTotality.

Import ListNotations.
Open Scope string_scope.

(* These controls inspect the new recursive carrier, not merely its lossless
   tree erasure. The universal derivation theorem remains the primary result. *)

Fixpoint phase1_grouping_example_count
  (tree : Phase1SurfaceRecursiveGroupingTree) : nat :=
  match tree with
  | Phase1GroupingNonterminal _ body
  | Phase1GroupingAlternative _ body
  | Phase1GroupingOptionalSome body => phase1_grouping_example_count body
  | Phase1GroupingSequence items | Phase1GroupingRepetition items =>
      fold_right
        (fun item total => phase1_grouping_example_count item + total)
        0 items
  | Phase1GroupingExpression expression =>
      phase1_grouping_example_expression_count expression
  | Phase1GroupingParenthesized expression =>
      S (phase1_grouping_example_expression_count expression)
  | Phase1GroupingTuple first second rest =>
      S (phase1_grouping_example_expression_count first +
         phase1_grouping_example_expression_count second +
         fold_right
           (fun expression total =>
             phase1_grouping_example_expression_count expression + total)
           0 rest)
  | _ => 0
  end

with phase1_grouping_example_expression_count
  (expression : Phase1SurfaceRecursiveGroupingExpression) : nat :=
  match expression with
  | Phase1GroupingExpressionValue base _ => phase1_grouping_example_count base
  end.

Definition phase1_grouping_example_primary_expression
  (primary : ParseTree) : ParseTree :=
  PTNonterminal "expression"
    (PTSequence
      [ PTNonterminal "base_expression"
          (PTAlternative 1
            (PTNonterminal "shift_expression"
              (PTSequence
                [ PTNonterminal "additive_expression"
                    (PTSequence
                      [ PTNonterminal "multiplicative_expression"
                          (PTSequence
                            [ PTNonterminal "unary_expression"
                                (PTAlternative 1
                                  (PTNonterminal "postfix_expression"
                                    (PTAlternative 1
                                      (PTSequence [primary; PTRepetition []]))));
                              PTRepetition [] ]);
                        PTRepetition [] ]);
                  PTRepetition [] ])));
        PTOptionalNone ]).

Definition phase1_grouping_example_integer (value : string) : ParseTree :=
  phase1_grouping_example_primary_expression
    (PTNonterminal "primary_expression"
      (PTAlternative 8
        (PTNonterminal "integer_literal" (PTLexical "DECIMAL_INTEGER" value)))).

Definition phase1_grouping_example_parenthesized
  (expression : ParseTree) : ParseTree :=
  phase1_grouping_example_primary_expression
    (PTNonterminal "primary_expression"
      (PTAlternative 1
        (PTNonterminal "parenthesized_expression"
          (PTSequence [PTLiteral "("; expression; PTLiteral ")"])))).

Definition phase1_grouping_example_tuple
  (first second : ParseTree) (rest : list ParseTree) : ParseTree :=
  phase1_grouping_example_primary_expression
    (PTNonterminal "primary_expression"
      (PTAlternative 0
        (PTNonterminal "tuple_expression"
          (PTSequence
            [ PTLiteral "("; first; PTLiteral ","; second;
              PTRepetition
                (map
                  (fun expression => PTSequence [PTLiteral ","; expression])
                  rest);
              PTLiteral ")" ])))).

Definition phase1_grouping_example_nested : ParseTree :=
  phase1_grouping_example_parenthesized
    (phase1_grouping_example_tuple
      (phase1_grouping_example_parenthesized (phase1_grouping_example_integer "1"))
      (phase1_grouping_example_tuple
        (phase1_grouping_example_integer "2")
        (phase1_grouping_example_parenthesized
          (phase1_grouping_example_integer "3")) [])
      [phase1_grouping_example_parenthesized
        (phase1_grouping_example_integer "4")]).

Fixpoint phase1_grouping_example_tokens (tree : ParseTree)
  : list ConcreteToken :=
  match tree with
  | PTLiteral literal => [TLiteral literal]
  | PTLexical class lexeme => [TLexical class lexeme]
  | PTNonterminal _ body | PTAlternative _ body | PTOptionalSome body =>
      phase1_grouping_example_tokens body
  | PTSequence items | PTRepetition items =>
      flat_map phase1_grouping_example_tokens items
  | PTOptionalNone => []
  end.

Example phase1_grouping_nested_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "expression")
    (phase1_grouping_example_tokens phase1_grouping_example_nested) []
    phase1_grouping_example_nested.
Proof.
  unfold phase1_grouping_example_nested, phase1_grouping_example_parenthesized,
    phase1_grouping_example_tuple, phase1_grouping_example_integer,
    phase1_grouping_example_primary_expression.
  cbn [phase1_grouping_example_tokens].
  repeat first
    [ match goal with
      | |- lookupRule _ _ = _ => vm_compute; reflexivity
      | |- nth_error _ _ = _ => reflexivity
      end
    | econstructor
    | discriminate ].
Qed.

Example phase1_grouping_nested_payloads_are_recursive :
  match phase1_surface_normalize_recursive_grouping_fuel
    (phase1_surface_grouping_tree_size phase1_grouping_example_nested)
    phase1_grouping_example_nested with
  | Some converted => phase1_grouping_example_count converted = 6
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_grouping_nested_reconstruction_is_exact :
  match phase1_surface_normalize_recursive_grouping_fuel
    (phase1_surface_grouping_tree_size phase1_grouping_example_nested)
    phase1_grouping_example_nested with
  | Some converted =>
      phase1_surface_recursive_grouping_tree converted =
        phase1_grouping_example_nested
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Definition phase1_grouping_example_named_arguments : ParseTree :=
  PTNonterminal "term_arguments"
    (PTSequence
      [ PTLiteral "(";
        PTOptionalSome
          (PTSequence
            [ phase1_grouping_example_parenthesized
                (phase1_grouping_example_integer "5");
              PTRepetition
                [PTSequence
                  [ PTLiteral ",";
                    phase1_grouping_example_tuple
                      (phase1_grouping_example_integer "6")
                      (phase1_grouping_example_integer "7") [] ]] ]);
        PTLiteral ")" ]).

Example phase1_grouping_traversal_reaches_generic_argument_shells :
  match phase1_surface_normalize_recursive_grouping_fuel
    (phase1_surface_grouping_tree_size phase1_grouping_example_named_arguments)
    phase1_grouping_example_named_arguments with
  | Some converted => phase1_grouping_example_count converted = 2
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Definition phase1_grouping_example_malformed : ParseTree :=
  PTNonterminal "parenthesized_expression"
    (PTSequence
      [ PTLiteral "(";
        phase1_grouping_example_integer "8";
        PTLiteral "]" ]).

Example phase1_grouping_rejects_malformed_nested_grouping :
  phase1_surface_normalize_recursive_grouping_fuel
    100
    (PTNonterminal "postfix_expression"
      (PTAlternative 1
        (PTSequence
          [ PTNonterminal "primary_expression"
              (PTAlternative 1 phase1_grouping_example_malformed);
            PTRepetition [] ]))) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_grouping_retains_command_boundary_exactly :
  phase1_surface_normalize_recursive_grouping_fuel 1
    (PTNonterminal "command_expression" phase1_grouping_example_malformed) =
  Some (Phase1GroupingCommandBoundary phase1_grouping_example_malformed).
Proof. reflexivity. Qed.

Example phase1_grouping_retains_fallback_boundary_exactly :
  phase1_surface_normalize_recursive_grouping_fuel 1
    (PTNonterminal "fallback" phase1_grouping_example_malformed) =
  Some (Phase1GroupingFallbackBoundary phase1_grouping_example_malformed).
Proof. reflexivity. Qed.

Example phase1_grouping_zero_fuel_is_not_a_success :
  phase1_surface_normalize_recursive_grouping_fuel 0
    phase1_grouping_example_nested = None.
Proof. reflexivity. Qed.
