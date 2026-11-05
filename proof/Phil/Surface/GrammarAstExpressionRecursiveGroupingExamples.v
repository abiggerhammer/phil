From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingTotality
  GrammarAstRecursiveGroupingExamples
  GrammarAstArithmeticRecursiveGroupingExamples
  GrammarAstShiftExpressionRecursiveGroupingSpine
  GrammarAstBaseExpressionChoiceSpine
  GrammarAstFallbackBaseChoiceSpine
  GrammarAstExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstBaseExpressionRecursiveGroupingSpine
  GrammarAstFallbackRecursiveGroupingSpine
  GrammarAstExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Inspect both independently refined arithmetic-bearing fields of the outer
   expression shell. The fixtures establish grammar structure, not operand
   typing or arithmetic evaluation. Command/failure-target payloads and the
   generic grouping carrier's nested fallback boundary remain exact trees. *)

Definition phase1_expression_grouping_example_shift_base
  (shift : ParseTree) : ParseTree :=
  PTNonterminal "base_expression" (PTAlternative 1 shift).

Definition phase1_expression_grouping_example_command_base
  (command : ParseTree) : ParseTree :=
  PTNonterminal "base_expression" (PTAlternative 0 command).

Definition phase1_expression_grouping_example_reject
  (base : ParseTree) : ParseTree :=
  PTNonterminal "fallback"
    (PTAlternative 1 (PTSequence [PTLiteral "reject"; base])).

Definition phase1_expression_grouping_example_fail
  (target : ParseTree) : ParseTree :=
  PTNonterminal "fallback"
    (PTAlternative 0 (PTSequence [PTLiteral "fail"; target])).

Definition phase1_expression_grouping_example_expression
  (base : ParseTree) (fallback : option ParseTree) : ParseTree :=
  PTNonterminal "expression"
    (PTSequence
      [base;
       match fallback with
       | None => PTOptionalNone
       | Some value =>
           PTOptionalSome (PTSequence [PTLiteral "or"; value])
       end]).

Definition phase1_expression_grouping_example_reject_shift : ParseTree :=
  phase1_arithmetic_grouping_example_chain "shift_expression"
    (phase1_arithmetic_grouping_example_chain "additive_expression"
      (phase1_arithmetic_grouping_example_chain "multiplicative_expression"
        (phase1_arithmetic_grouping_example_unary 7
          (phase1_arithmetic_grouping_example_parenthesized
            phase1_grouping_example_nested)) []) []) [].

Definition phase1_expression_grouping_example_reject_fixture : ParseTree :=
  phase1_expression_grouping_example_expression
    (phase1_expression_grouping_example_shift_base
      phase1_arithmetic_grouping_example_shift)
    (Some (phase1_expression_grouping_example_reject
      (phase1_expression_grouping_example_shift_base
        phase1_expression_grouping_example_reject_shift))).

Example phase1_expression_grouping_reject_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "expression")
    (phase1_grouping_example_tokens
      phase1_expression_grouping_example_reject_fixture) []
    phase1_expression_grouping_example_reject_fixture.
Proof.
  unfold phase1_expression_grouping_example_reject_fixture,
    phase1_expression_grouping_example_expression,
    phase1_expression_grouping_example_shift_base,
    phase1_expression_grouping_example_reject,
    phase1_expression_grouping_example_reject_shift,
    phase1_arithmetic_grouping_example_shift,
    phase1_arithmetic_grouping_example_additive,
    phase1_arithmetic_grouping_example_multiplicative,
    phase1_arithmetic_grouping_example_chain,
    phase1_arithmetic_grouping_example_suffix,
    phase1_arithmetic_grouping_example_unary,
    phase1_arithmetic_grouping_example_parenthesized,
    phase1_arithmetic_grouping_example_tuple,
    phase1_grouping_example_nested, phase1_grouping_example_parenthesized,
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

Definition phase1_expression_grouping_has_distinct_refined_fields
  (expression : Phase1SurfaceExpressionRecursiveGroupingSpine) : Prop :=
  match phase1_expression_recursive_grouping_spine_base expression,
        phase1_expression_recursive_grouping_spine_fallback expression with
  | Phase1BaseGroupingShift main,
    Some (Phase1FallbackGroupingReject (Phase1BaseGroupingShift rejected)) =>
      phase1_arithmetic_grouping_shift_shapes main =
        [ [ [(3, 1); (1, 1); (2, 2); (0, 1)]; [(2, 1)]; [(1, 2)] ];
          [ [(0, 1)] ];
          [ [(4, 1)] ] ] /\
      phase1_arithmetic_grouping_shift_shapes rejected = [ [ [(7, 7)] ] ]
  | _, _ => False
  end.

Example phase1_expression_grouping_replaces_main_and_reject_operands :
  match phase1_surface_normalize_expression_recursive_grouping_tree
    phase1_expression_grouping_example_reject_fixture with
  | Some refined => phase1_expression_grouping_has_distinct_refined_fields refined
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example phase1_expression_grouping_reconstructs_the_whole_expression :
  match phase1_surface_normalize_expression_recursive_grouping_tree
    phase1_expression_grouping_example_reject_fixture with
  | Some refined =>
      phase1_surface_expression_recursive_grouping_spine_tree refined =
        phase1_expression_grouping_example_reject_fixture
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* This is a concrete compatibility control. Its supplied node-count fuel is
   not a universal bound theorem for the old shared-fuel normalizer. *)
Example phase1_expression_grouping_legacy_adapter_replaces_both_fields :
  match
    phase1_surface_normalize_expression_fallback_base_choice_shift_refined_tree_fuel
      (phase1_surface_grouping_tree_size
        phase1_expression_grouping_example_reject_fixture)
      phase1_expression_grouping_example_reject_fixture
  with
  | Some previous =>
      match phase1_surface_refine_expression_recursive_grouping previous with
      | Some refined =>
          phase1_expression_grouping_has_distinct_refined_fields refined /\
          phase1_surface_expression_recursive_grouping_spine_tree refined =
            phase1_expression_grouping_example_reject_fixture
      | None => False
      end
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_expression_grouping_legacy_fallback_adapter_refines_reject :
  match phase1_surface_refine_fallback_recursive_grouping
    (Phase1FallbackBaseChoiceReject
      (Phase1BaseExpressionShift phase1_expression_grouping_example_reject_shift))
  with
  | Some (Phase1FallbackGroupingReject (Phase1BaseGroupingShift refined)) =>
      phase1_arithmetic_grouping_shift_shapes refined = [ [ [(7, 7)] ] ]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_expression_grouping_preserves_absent_fallback :
  match phase1_surface_normalize_expression_recursive_grouping_tree
    (phase1_expression_grouping_example_expression
      (phase1_expression_grouping_example_shift_base
        phase1_expression_grouping_example_reject_shift) None)
  with
  | Some refined =>
      phase1_expression_recursive_grouping_spine_fallback refined = None /\
      match phase1_expression_recursive_grouping_spine_base refined with
      | Phase1BaseGroupingShift operand =>
          phase1_arithmetic_grouping_shift_shapes operand = [ [ [(7, 7)] ] ]
      | _ => False
      end
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Definition phase1_expression_grouping_example_command : ParseTree :=
  PTNonterminal "command_expression"
    (PTAlternative 7
      (PTNonterminal "continue_expression"
        (PTSequence [PTLiteral "continue"; PTOptionalNone]))).

Definition phase1_expression_grouping_example_failure_target : ParseTree :=
  PTNonterminal "failure_target"
    (PTSequence
      [ PTNonterminal "static_reference"
          (PTSequence
            [ PTNonterminal "qualified_name"
                (PTSequence
                  [PTNonterminal "identifier" (PTLexical "IDENTIFIER" "Oops");
                   PTRepetition []]);
              PTOptionalNone ]);
        PTOptionalSome phase1_grouping_example_named_arguments ]).

Definition phase1_expression_grouping_example_command_fail_fixture : ParseTree :=
  phase1_expression_grouping_example_expression
    (phase1_expression_grouping_example_command_base
      phase1_expression_grouping_example_command)
    (Some (phase1_expression_grouping_example_fail
      phase1_expression_grouping_example_failure_target)).

Example phase1_expression_grouping_command_fail_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "expression")
    (phase1_grouping_example_tokens
      phase1_expression_grouping_example_command_fail_fixture) []
    phase1_expression_grouping_example_command_fail_fixture.
Proof.
  unfold phase1_expression_grouping_example_command_fail_fixture,
    phase1_expression_grouping_example_expression,
    phase1_expression_grouping_example_command_base,
    phase1_expression_grouping_example_command,
    phase1_expression_grouping_example_fail,
    phase1_expression_grouping_example_failure_target,
    phase1_grouping_example_named_arguments,
    phase1_grouping_example_parenthesized,
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

Example phase1_expression_grouping_preserves_command_and_fail_target_exactly :
  phase1_surface_normalize_expression_recursive_grouping_tree
    phase1_expression_grouping_example_command_fail_fixture =
  Some
    {| phase1_expression_recursive_grouping_spine_base :=
         Phase1BaseGroupingCommand phase1_expression_grouping_example_command;
       phase1_expression_recursive_grouping_spine_fallback :=
         Some (Phase1FallbackGroupingFail
           phase1_expression_grouping_example_failure_target) |}.
Proof. vm_compute. reflexivity. Qed.

Example phase1_expression_grouping_preserves_reject_command_exactly :
  phase1_surface_normalize_expression_recursive_grouping_tree
    (phase1_expression_grouping_example_expression
      (phase1_expression_grouping_example_command_base
        phase1_expression_grouping_example_command)
      (Some (phase1_expression_grouping_example_reject
        (phase1_expression_grouping_example_command_base
          phase1_expression_grouping_example_command)))) =
  Some
    {| phase1_expression_recursive_grouping_spine_base :=
         Phase1BaseGroupingCommand phase1_expression_grouping_example_command;
       phase1_expression_recursive_grouping_spine_fallback :=
         Some (Phase1FallbackGroupingReject
           (Phase1BaseGroupingCommand phase1_expression_grouping_example_command)) |}.
Proof. vm_compute. reflexivity. Qed.

Example phase1_expression_grouping_rejects_wrong_optional_keyword :
  phase1_surface_normalize_expression_recursive_grouping_tree
    (PTNonterminal "expression"
      (PTSequence
        [phase1_expression_grouping_example_shift_base
           phase1_arithmetic_grouping_example_shift;
         PTOptionalSome
           (PTSequence
             [PTLiteral "else";
              phase1_expression_grouping_example_reject
                (phase1_expression_grouping_example_shift_base
                  phase1_expression_grouping_example_reject_shift)])])) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_expression_grouping_rejects_mismatched_fallback_keyword :
  phase1_surface_normalize_fallback_recursive_grouping_tree
    (PTNonterminal "fallback"
      (PTAlternative 1
        (PTSequence
          [PTLiteral "fail";
           phase1_expression_grouping_example_shift_base
             phase1_expression_grouping_example_reject_shift]))) = None.
Proof. vm_compute. reflexivity. Qed.

Definition phase1_expression_grouping_example_bad_shift : ParseTree :=
  phase1_arithmetic_grouping_example_chain "shift_expression"
    phase1_arithmetic_grouping_example_additive
    [ phase1_arithmetic_grouping_example_suffix 0 "<<"
        phase1_arithmetic_grouping_example_additive;
      phase1_arithmetic_grouping_example_suffix 1 ">>"
        phase1_arithmetic_grouping_example_bad_additive_operand ].

Example phase1_expression_grouping_rejects_malformed_main_operand :
  phase1_surface_normalize_expression_recursive_grouping_tree
    (phase1_expression_grouping_example_expression
      (phase1_expression_grouping_example_shift_base
        phase1_expression_grouping_example_bad_shift)
      (Some (phase1_expression_grouping_example_reject
        (phase1_expression_grouping_example_shift_base
          phase1_expression_grouping_example_reject_shift)))) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_expression_grouping_rejects_malformed_reject_operand :
  phase1_surface_normalize_expression_recursive_grouping_tree
    (phase1_expression_grouping_example_expression
      (phase1_expression_grouping_example_shift_base
        phase1_arithmetic_grouping_example_shift)
      (Some (phase1_expression_grouping_example_reject
        (phase1_expression_grouping_example_shift_base
          phase1_expression_grouping_example_bad_shift)))) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_expression_grouping_legacy_fallback_rejects_invalid_erasure :
  phase1_surface_refine_fallback_recursive_grouping
    (Phase1FallbackBaseChoiceReject
      (Phase1BaseExpressionShift phase1_expression_grouping_example_bad_shift)) =
  None.
Proof. vm_compute. reflexivity. Qed.
