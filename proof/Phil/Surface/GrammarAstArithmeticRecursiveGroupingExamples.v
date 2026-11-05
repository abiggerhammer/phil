From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingTotality
  GrammarAstRecursiveGroupingExamples
  GrammarAstPrimaryExpressionRecursiveGroupingSpine
  GrammarAstPostfixExpressionRefinedSpine
  GrammarAstPostfixExpressionRecursiveGroupingSpine
  GrammarAstPrimaryPostfixRecursiveGroupingExamples
  GrammarAstUnaryExpressionRecursiveRefinedSpine
  GrammarAstUnaryExpressionRecursiveGroupingSpine
  GrammarAstMultiplicativeExpressionSpine
  GrammarAstMultiplicativeExpressionRecursiveGroupingSpine
  GrammarAstAdditiveExpressionSpine
  GrammarAstAdditiveExpressionRecursiveGroupingSpine
  GrammarAstShiftExpressionSpine
  GrammarAstShiftExpressionRefinedSpine
  GrammarAstShiftExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Inspect typed operands at every precedence layer, including every repeated
   suffix position. These are structural grammar controls, not claims about
   arithmetic evaluation or the typing of the fixture's tuple operands. *)

Definition phase1_arithmetic_grouping_primary_count
  (primary : Phase1SurfacePrimaryExpressionRecursiveGroupingSpine) : nat :=
  match primary with
  | Phase1PrimaryGroupingTuple first second rest =>
      S (phase1_grouping_example_expression_count first +
         phase1_grouping_example_expression_count second +
         fold_right
           (fun expression total =>
             phase1_grouping_example_expression_count expression + total)
           0 rest)
  | Phase1PrimaryGroupingParenthesized expression =>
      S (phase1_grouping_example_expression_count expression)
  | _ => 0
  end.

Definition phase1_arithmetic_grouping_postfix_count
  (postfix : Phase1SurfacePostfixExpressionRecursiveGroupingSpine) : nat :=
  match postfix with
  | Phase1PostfixGroupingNamed _ => 0
  | Phase1PostfixGroupingPrimary primary _ =>
      phase1_arithmetic_grouping_primary_count primary
  end.

Fixpoint phase1_arithmetic_grouping_unary_shape
  (unary : Phase1SurfaceUnaryExpressionRecursiveGroupingSpine) : nat * nat :=
  match unary with
  | Phase1UnaryGroupingNegate operand =>
      let '(depth, groups) := phase1_arithmetic_grouping_unary_shape operand in
      (S depth, groups)
  | Phase1UnaryGroupingPostfix postfix =>
      (0, phase1_arithmetic_grouping_postfix_count postfix)
  end.

Definition phase1_arithmetic_grouping_multiplicative_shapes
  (expression : Phase1SurfaceMultiplicativeExpressionRecursiveGroupingSpine)
  : list (nat * nat) :=
  phase1_arithmetic_grouping_unary_shape
    (phase1_multiplicative_expression_recursive_grouping_spine_first expression) ::
  map
    (fun suffix => phase1_arithmetic_grouping_unary_shape
      (phase1_multiplicative_suffix_recursive_grouping_spine_right suffix))
    (phase1_multiplicative_expression_recursive_grouping_spine_rest expression).

Definition phase1_arithmetic_grouping_additive_shapes
  (expression : Phase1SurfaceAdditiveExpressionRecursiveGroupingSpine)
  : list (list (nat * nat)) :=
  phase1_arithmetic_grouping_multiplicative_shapes
    (phase1_additive_expression_recursive_grouping_spine_first expression) ::
  map
    (fun suffix => phase1_arithmetic_grouping_multiplicative_shapes
      (phase1_additive_suffix_recursive_grouping_spine_right suffix))
    (phase1_additive_expression_recursive_grouping_spine_rest expression).

Definition phase1_arithmetic_grouping_shift_shapes
  (expression : Phase1SurfaceShiftExpressionRecursiveGroupingSpine)
  : list (list (list (nat * nat))) :=
  phase1_arithmetic_grouping_additive_shapes
    (phase1_shift_expression_recursive_grouping_spine_first expression) ::
  map
    (fun suffix => phase1_arithmetic_grouping_additive_shapes
      (phase1_shift_suffix_recursive_grouping_spine_right suffix))
    (phase1_shift_expression_recursive_grouping_spine_rest expression).

Definition phase1_arithmetic_grouping_example_parenthesized
  (expression : ParseTree) : ParseTree :=
  PTNonterminal "primary_expression"
    (PTAlternative 1
      (PTNonterminal "parenthesized_expression"
        (PTSequence [PTLiteral "("; expression; PTLiteral ")"]))).

Definition phase1_arithmetic_grouping_example_tuple
  (first second : ParseTree) : ParseTree :=
  PTNonterminal "primary_expression"
    (PTAlternative 0
      (PTNonterminal "tuple_expression"
        (PTSequence
          [PTLiteral "("; first; PTLiteral ","; second;
           PTRepetition []; PTLiteral ")"]))).

Fixpoint phase1_arithmetic_grouping_example_negations
  (depth : nat) (operand : ParseTree) : ParseTree :=
  match depth with
  | O => operand
  | S remaining =>
      PTNonterminal "unary_expression"
        (PTAlternative 0
          (PTSequence
            [PTLiteral "-";
             phase1_arithmetic_grouping_example_negations remaining operand]))
  end.

Definition phase1_arithmetic_grouping_example_unary
  (depth : nat) (primary : ParseTree) : ParseTree :=
  phase1_arithmetic_grouping_example_negations depth
    (PTNonterminal "unary_expression"
      (PTAlternative 1
        (PTNonterminal "postfix_expression"
          (PTAlternative 1 (PTSequence [primary; PTRepetition []]))))).

Definition phase1_arithmetic_grouping_example_suffix
  (branch : nat) (operator : string) (right_operand : ParseTree) : ParseTree :=
  PTSequence [PTAlternative branch (PTLiteral operator); right_operand].

Definition phase1_arithmetic_grouping_example_chain
  (name : string) (first : ParseTree) (rest : list ParseTree) : ParseTree :=
  PTNonterminal name (PTSequence [first; PTRepetition rest]).

Definition phase1_arithmetic_grouping_example_multiplicative : ParseTree :=
  phase1_arithmetic_grouping_example_chain "multiplicative_expression"
    (phase1_arithmetic_grouping_example_unary 3
      (phase1_arithmetic_grouping_example_parenthesized
        (phase1_grouping_example_integer "1")))
    [ phase1_arithmetic_grouping_example_suffix 0 "*"
        (phase1_arithmetic_grouping_example_unary 1
          (phase1_arithmetic_grouping_example_tuple
            (phase1_grouping_example_integer "2")
            (phase1_grouping_example_integer "3")));
      phase1_arithmetic_grouping_example_suffix 1 "/"
        (phase1_arithmetic_grouping_example_unary 2
          (phase1_arithmetic_grouping_example_parenthesized
            (phase1_grouping_example_tuple
              (phase1_grouping_example_integer "4")
              (phase1_grouping_example_integer "5") [])));
      phase1_arithmetic_grouping_example_suffix 2 "%"
        (phase1_arithmetic_grouping_example_unary 0
          (phase1_arithmetic_grouping_example_parenthesized
            (phase1_grouping_example_integer "6"))) ].

Definition phase1_arithmetic_grouping_example_additive : ParseTree :=
  phase1_arithmetic_grouping_example_chain "additive_expression"
    phase1_arithmetic_grouping_example_multiplicative
    [ phase1_arithmetic_grouping_example_suffix 0 "+"
        (phase1_arithmetic_grouping_example_chain "multiplicative_expression"
          (phase1_arithmetic_grouping_example_unary 2
            (phase1_arithmetic_grouping_example_tuple
              (phase1_grouping_example_integer "7")
              (phase1_grouping_example_integer "8"))) []);
      phase1_arithmetic_grouping_example_suffix 1 "-"
        (phase1_arithmetic_grouping_example_chain "multiplicative_expression"
          (phase1_arithmetic_grouping_example_unary 1
            (phase1_arithmetic_grouping_example_parenthesized
              (phase1_grouping_example_parenthesized
                (phase1_grouping_example_integer "9")))) []) ].

Definition phase1_arithmetic_grouping_example_shift : ParseTree :=
  phase1_arithmetic_grouping_example_chain "shift_expression"
    phase1_arithmetic_grouping_example_additive
    [ phase1_arithmetic_grouping_example_suffix 0 "<<"
        (phase1_arithmetic_grouping_example_chain "additive_expression"
          (phase1_arithmetic_grouping_example_chain "multiplicative_expression"
            (phase1_arithmetic_grouping_example_unary 0
              (phase1_arithmetic_grouping_example_parenthesized
                (phase1_grouping_example_integer "10"))) []) []);
      phase1_arithmetic_grouping_example_suffix 1 ">>"
        (phase1_arithmetic_grouping_example_chain "additive_expression"
          (phase1_arithmetic_grouping_example_chain "multiplicative_expression"
            (phase1_arithmetic_grouping_example_unary 4
              (phase1_arithmetic_grouping_example_tuple
                (phase1_grouping_example_integer "11")
                (phase1_grouping_example_integer "12"))) []) []) ].

Example phase1_arithmetic_grouping_shift_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "shift_expression")
    (phase1_grouping_example_tokens phase1_arithmetic_grouping_example_shift) []
    phase1_arithmetic_grouping_example_shift.
Proof.
  unfold phase1_arithmetic_grouping_example_shift,
    phase1_arithmetic_grouping_example_additive,
    phase1_arithmetic_grouping_example_multiplicative,
    phase1_arithmetic_grouping_example_chain,
    phase1_arithmetic_grouping_example_suffix,
    phase1_arithmetic_grouping_example_unary,
    phase1_arithmetic_grouping_example_parenthesized,
    phase1_arithmetic_grouping_example_tuple,
    phase1_grouping_example_parenthesized,
    phase1_grouping_example_tuple, phase1_grouping_example_integer,
    phase1_grouping_example_primary_expression.
  cbn [phase1_arithmetic_grouping_example_negations
    phase1_grouping_example_tokens].
  repeat first
    [ match goal with
      | |- lookupRule _ _ = _ => vm_compute; reflexivity
      | |- nth_error _ _ = _ => reflexivity
      end
    | econstructor
    | discriminate ].
Qed.

Example phase1_arithmetic_grouping_replaces_every_operand :
  match phase1_surface_normalize_shift_expression_recursive_grouping_tree
    phase1_arithmetic_grouping_example_shift with
  | Some refined =>
      phase1_arithmetic_grouping_shift_shapes refined =
        [ [ [(3, 1); (1, 1); (2, 2); (0, 1)]; [(2, 1)]; [(1, 2)] ];
          [ [(0, 1)] ];
          [ [(4, 1)] ] ]
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_arithmetic_grouping_keeps_multiplicative_operator_order :
  match phase1_surface_normalize_multiplicative_expression_recursive_grouping_tree
    phase1_arithmetic_grouping_example_multiplicative with
  | Some refined =>
      map phase1_multiplicative_suffix_recursive_grouping_spine_operator
        (phase1_multiplicative_expression_recursive_grouping_spine_rest refined) =
        [Phase1SurfaceMultiplicativeOperatorMultiply;
         Phase1SurfaceMultiplicativeOperatorDivide;
         Phase1SurfaceMultiplicativeOperatorRemainder]
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_arithmetic_grouping_keeps_additive_operator_order :
  match phase1_surface_normalize_additive_expression_recursive_grouping_tree
    phase1_arithmetic_grouping_example_additive with
  | Some refined =>
      map phase1_additive_suffix_recursive_grouping_spine_operator
        (phase1_additive_expression_recursive_grouping_spine_rest refined) =
        [Phase1SurfaceAdditiveOperatorPlus; Phase1SurfaceAdditiveOperatorMinus]
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_arithmetic_grouping_keeps_shift_operator_order :
  match phase1_surface_normalize_shift_expression_recursive_grouping_tree
    phase1_arithmetic_grouping_example_shift with
  | Some refined =>
      map phase1_shift_suffix_recursive_grouping_spine_operator
        (phase1_shift_expression_recursive_grouping_spine_rest refined) =
        [Phase1SurfaceShiftOperatorLeft; Phase1SurfaceShiftOperatorRight]
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_arithmetic_grouping_reconstructs_the_whole_precedence_tree :
  match phase1_surface_normalize_shift_expression_recursive_grouping_tree
    phase1_arithmetic_grouping_example_shift with
  | Some refined =>
      phase1_surface_shift_expression_recursive_grouping_spine_tree refined =
        phase1_arithmetic_grouping_example_shift
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Definition phase1_arithmetic_grouping_example_deep_unary : ParseTree :=
  phase1_arithmetic_grouping_example_negations 12
    (PTNonterminal "unary_expression"
      (PTAlternative 1 phase1_postfix_grouping_example_tuple_projections)).

Example phase1_arithmetic_grouping_computed_fuel_handles_deep_unary :
  match phase1_surface_normalize_unary_expression_recursive_grouping_tree
    phase1_arithmetic_grouping_example_deep_unary with
  | Some refined => phase1_arithmetic_grouping_unary_shape refined = (12, 5)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_arithmetic_grouping_zero_unary_fuel_is_not_a_success :
  phase1_surface_normalize_unary_expression_recursive_grouping_tree_fuel
    0 phase1_arithmetic_grouping_example_deep_unary = None.
Proof. reflexivity. Qed.

Fixpoint phase1_arithmetic_grouping_legacy_negations
  (depth : nat) (operand : Phase1SurfaceUnaryExpressionRecursiveRefinedSpine)
  : Phase1SurfaceUnaryExpressionRecursiveRefinedSpine :=
  match depth with
  | O => operand
  | S remaining => Phase1SurfaceUnaryExpressionNegateRecursiveRefined
      (phase1_arithmetic_grouping_legacy_negations remaining operand)
  end.

Example phase1_arithmetic_grouping_legacy_unary_canonicalizes_retained_primary :
  match phase1_surface_refine_unary_expression_recursive_grouping
    (phase1_arithmetic_grouping_legacy_negations 3
      (Phase1SurfaceUnaryExpressionPostfixRecursiveRefined
        (Phase1SurfacePostfixExpressionPrimaryRefined
          (phase1_primary_grouping_example_legacy_retained 1
            (PTNonterminal "parenthesized_expression"
              (PTSequence
                [PTLiteral "("; phase1_grouping_example_integer "1";
                 PTLiteral ")"]))) ["value"]))) with
  | Some refined => phase1_arithmetic_grouping_unary_shape refined = (3, 1)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_arithmetic_grouping_legacy_shift_adapter_reconstructs_exactly :
  match phase1_surface_normalize_shift_expression_refined_tree_fuel
    (phase1_surface_grouping_tree_size phase1_arithmetic_grouping_example_shift)
    phase1_arithmetic_grouping_example_shift with
  | Some previous =>
      match phase1_surface_refine_shift_expression_recursive_grouping previous with
      | Some refined =>
          phase1_surface_shift_expression_recursive_grouping_spine_tree refined =
            phase1_arithmetic_grouping_example_shift
      | None => False
      end
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_arithmetic_grouping_rejects_wrong_unary_marker :
  phase1_surface_normalize_unary_expression_recursive_grouping_tree
    (PTNonterminal "unary_expression"
      (PTAlternative 0
        (PTSequence
          [PTLiteral "+"; phase1_arithmetic_grouping_example_deep_unary]))) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_arithmetic_grouping_rejects_mismatched_operator_branch :
  phase1_surface_normalize_multiplicative_expression_recursive_grouping_tree
    (phase1_arithmetic_grouping_example_chain "multiplicative_expression"
      (phase1_arithmetic_grouping_example_unary 0
        (phase1_arithmetic_grouping_example_parenthesized
          (phase1_grouping_example_integer "1")))
      [phase1_arithmetic_grouping_example_suffix 2 "/"
        (phase1_arithmetic_grouping_example_unary 0
          (phase1_arithmetic_grouping_example_parenthesized
            (phase1_grouping_example_integer "2")))]) = None.
Proof. vm_compute. reflexivity. Qed.

Definition phase1_arithmetic_grouping_example_bad_additive_operand : ParseTree :=
  phase1_arithmetic_grouping_example_chain "additive_expression"
    (phase1_arithmetic_grouping_example_chain "multiplicative_expression"
      (phase1_arithmetic_grouping_example_unary 2
        (PTNonterminal "primary_expression"
          (PTAlternative 1 phase1_grouping_example_malformed))) []) [].

Example phase1_arithmetic_grouping_rejects_malformed_later_suffix_operand :
  phase1_surface_normalize_shift_expression_recursive_grouping_tree
    (phase1_arithmetic_grouping_example_chain "shift_expression"
      phase1_arithmetic_grouping_example_additive
      [ phase1_arithmetic_grouping_example_suffix 0 "<<"
          phase1_arithmetic_grouping_example_additive;
        phase1_arithmetic_grouping_example_suffix 1 ">>"
          phase1_arithmetic_grouping_example_bad_additive_operand ]) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_arithmetic_grouping_preserves_named_leaf_through_negation :
  forall named,
    phase1_surface_refine_unary_expression_recursive_grouping
      (phase1_arithmetic_grouping_legacy_negations 2
        (Phase1SurfaceUnaryExpressionPostfixRecursiveRefined
          (Phase1SurfacePostfixExpressionNamedFullyRefined named))) =
    Some (Phase1UnaryGroupingNegate
      (Phase1UnaryGroupingNegate
        (Phase1UnaryGroupingPostfix (Phase1PostfixGroupingNamed named)))).
Proof. reflexivity. Qed.
