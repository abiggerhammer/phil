From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingTotality
  GrammarAstRecursiveGroupingExamples
  GrammarAstArithmeticRecursiveGroupingExamples
  GrammarAstExpressionRecursiveGroupingExamples
  GrammarAstBaseExpressionRecursiveGroupingSpine
  GrammarAstFallbackRecursiveGroupingSpine
  GrammarAstExpressionRecursiveGroupingSpine
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstTermArgumentsRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Inspect every element of the selected outer argument list. Empty means the
   present syntax (); optional absence belongs to an enclosing consumer.
   The fixture's tuple operands establish grammar structure, not typing or
   arithmetic evaluation. Existing nested retained boundaries remain exact. *)

Definition phase1_term_arguments_grouping_example_tree
  (arguments : list ParseTree) : ParseTree :=
  PTNonterminal "term_arguments"
    (PTSequence
      [PTLiteral "(";
       match arguments with
       | [] => PTOptionalNone
       | first :: rest =>
           PTOptionalSome
             (PTSequence
               [first;
                PTRepetition
                  (map (fun argument => PTSequence [PTLiteral ","; argument])
                    rest)])
       end;
       PTLiteral ")"]).

Definition phase1_term_arguments_grouping_example_first : ParseTree :=
  phase1_expression_grouping_example_expression
    (phase1_expression_grouping_example_shift_base
      phase1_expression_grouping_example_reject_shift) None.

Definition phase1_term_arguments_grouping_example_values : list ParseTree :=
  [phase1_term_arguments_grouping_example_first;
   phase1_expression_grouping_example_command_fail_fixture;
   phase1_expression_grouping_example_reject_fixture].

Definition phase1_term_arguments_grouping_example_mixed : ParseTree :=
  phase1_term_arguments_grouping_example_tree
    phase1_term_arguments_grouping_example_values.

Example phase1_term_arguments_grouping_empty_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "term_arguments")
    [TLiteral "("; TLiteral ")"] []
    (phase1_term_arguments_grouping_example_tree []).
Proof.
  unfold phase1_term_arguments_grouping_example_tree.
  repeat first
    [ match goal with
      | |- lookupRule _ _ = _ => vm_compute; reflexivity
      | |- nth_error _ _ = _ => reflexivity
      end
    | econstructor
    | discriminate ].
Qed.

Example phase1_term_arguments_grouping_preserves_empty_parentheses :
  phase1_surface_normalize_term_arguments_recursive_grouping_tree
    (phase1_term_arguments_grouping_example_tree []) =
  Some {| phase1_term_arguments_recursive_grouping_spine_arguments := [] |}.
Proof. vm_compute. reflexivity. Qed.

Example phase1_term_arguments_grouping_mixed_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "term_arguments")
    (phase1_grouping_example_tokens phase1_term_arguments_grouping_example_mixed)
    [] phase1_term_arguments_grouping_example_mixed.
Proof.
  unfold phase1_term_arguments_grouping_example_mixed,
    phase1_term_arguments_grouping_example_values,
    phase1_term_arguments_grouping_example_tree,
    phase1_term_arguments_grouping_example_first,
    phase1_expression_grouping_example_reject_fixture,
    phase1_expression_grouping_example_command_fail_fixture,
    phase1_expression_grouping_example_expression,
    phase1_expression_grouping_example_shift_base,
    phase1_expression_grouping_example_command_base,
    phase1_expression_grouping_example_command,
    phase1_expression_grouping_example_fail,
    phase1_expression_grouping_example_failure_target,
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
    phase1_grouping_example_named_arguments,
    phase1_grouping_example_nested, phase1_grouping_example_parenthesized,
    phase1_grouping_example_tuple, phase1_grouping_example_integer,
    phase1_grouping_example_primary_expression.
  cbn [map phase1_arithmetic_grouping_example_negations
    phase1_grouping_example_tokens].
  repeat first
    [ match goal with
      | |- lookupRule _ _ = _ => vm_compute; reflexivity
      | |- nth_error _ _ = _ => reflexivity
      end
    | econstructor
    | discriminate ].
Qed.

Definition phase1_term_arguments_grouping_has_all_refined_values
  (arguments : Phase1SurfaceTermArgumentsRecursiveGroupingSpine) : Prop :=
  match phase1_term_arguments_recursive_grouping_spine_arguments arguments with
  | [first; middle; last] =>
      (match phase1_expression_recursive_grouping_spine_base first with
       | Phase1BaseGroupingShift shifted =>
           phase1_arithmetic_grouping_shift_shapes shifted = [ [ [(7, 7)] ] ]
       | _ => False
       end) /\
      phase1_expression_recursive_grouping_spine_fallback first = None /\
      middle =
        {| phase1_expression_recursive_grouping_spine_base :=
             Phase1BaseGroupingCommand phase1_expression_grouping_example_command;
           phase1_expression_recursive_grouping_spine_fallback :=
             Some (Phase1FallbackGroupingFail
               phase1_expression_grouping_example_failure_target) |} /\
      phase1_expression_grouping_has_distinct_refined_fields last
  | _ => False
  end.

Example phase1_term_arguments_grouping_replaces_every_argument_in_order :
  match phase1_surface_normalize_term_arguments_recursive_grouping_tree
    phase1_term_arguments_grouping_example_mixed with
  | Some refined => phase1_term_arguments_grouping_has_all_refined_values refined
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_term_arguments_grouping_preserves_the_complete_argument_list :
  match phase1_surface_normalize_term_arguments_recursive_grouping_tree
    phase1_term_arguments_grouping_example_mixed with
  | Some refined =>
      map phase1_surface_expression_recursive_grouping_spine_tree
        (phase1_term_arguments_recursive_grouping_spine_arguments refined) =
        phase1_term_arguments_grouping_example_values
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_term_arguments_grouping_reconstructs_exact_punctuation :
  match phase1_surface_normalize_term_arguments_recursive_grouping_tree
    phase1_term_arguments_grouping_example_mixed with
  | Some refined =>
      phase1_surface_term_arguments_recursive_grouping_spine_tree refined =
        phase1_term_arguments_grouping_example_mixed
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_term_arguments_grouping_preserves_singleton_main_and_reject :
  match phase1_surface_normalize_term_arguments_recursive_grouping_tree
    (phase1_term_arguments_grouping_example_tree
      [phase1_expression_grouping_example_reject_fixture]) with
  | Some refined =>
      match phase1_term_arguments_recursive_grouping_spine_arguments refined with
      | [only] => phase1_expression_grouping_has_distinct_refined_fields only
      | _ => False
      end
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(* Node-count fuel is a concrete regression input for the legacy decoder, not
   a universal sufficient-fuel theorem about its old shared-fuel machinery. *)
Example phase1_term_arguments_grouping_legacy_adapter_replaces_all_arguments :
  match
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_tree_fuel
      (phase1_surface_grouping_tree_size
        phase1_term_arguments_grouping_example_mixed)
      phase1_term_arguments_grouping_example_mixed
  with
  | Some previous =>
      match phase1_surface_refine_term_arguments_recursive_grouping previous with
      | Some refined =>
          phase1_term_arguments_grouping_has_all_refined_values refined /\
          phase1_surface_term_arguments_recursive_grouping_spine_tree refined =
            phase1_term_arguments_grouping_example_mixed
      | None => False
      end
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_term_arguments_grouping_rejects_malformed_middle_main :
  phase1_surface_normalize_term_arguments_recursive_grouping_tree
    (phase1_term_arguments_grouping_example_tree
      [phase1_term_arguments_grouping_example_first;
       phase1_expression_grouping_example_expression
         (phase1_expression_grouping_example_shift_base
           phase1_expression_grouping_example_bad_shift) None;
       phase1_expression_grouping_example_reject_fixture]) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_term_arguments_grouping_rejects_malformed_last_reject :
  phase1_surface_normalize_term_arguments_recursive_grouping_tree
    (phase1_term_arguments_grouping_example_tree
      [phase1_term_arguments_grouping_example_first;
       phase1_expression_grouping_example_command_fail_fixture;
       phase1_expression_grouping_example_expression
         (phase1_expression_grouping_example_shift_base
           phase1_expression_grouping_example_reject_shift)
         (Some (phase1_expression_grouping_example_reject
           (phase1_expression_grouping_example_shift_base
             phase1_expression_grouping_example_bad_shift)))]) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_term_arguments_grouping_rejects_wrong_separator :
  phase1_surface_normalize_term_arguments_recursive_grouping_tree
    (PTNonterminal "term_arguments"
      (PTSequence
        [PTLiteral "(";
         PTOptionalSome
           (PTSequence
             [phase1_term_arguments_grouping_example_first;
              PTRepetition
                [PTSequence [PTLiteral ";";
                  phase1_expression_grouping_example_reject_fixture]]]);
         PTLiteral ")"])) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_term_arguments_grouping_rejects_trailing_comma :
  phase1_surface_normalize_term_arguments_recursive_grouping_tree
    (PTNonterminal "term_arguments"
      (PTSequence
        [PTLiteral "(";
         PTOptionalSome
           (PTSequence
             [phase1_term_arguments_grouping_example_first;
              PTRepetition [PTSequence [PTLiteral ","]]]);
         PTLiteral ")"])) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_term_arguments_grouping_rejects_wrong_closing_delimiter :
  phase1_surface_normalize_term_arguments_recursive_grouping_tree
    (PTNonterminal "term_arguments"
      (PTSequence [PTLiteral "("; PTOptionalNone; PTLiteral "]"])) = None.
Proof. vm_compute. reflexivity. Qed.
