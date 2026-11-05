From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstSourceHeader
  GrammarAstStaticReferenceSpine
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingTotality
  GrammarAstRecursiveGroupingExamples
  GrammarAstExpressionRecursiveGroupingExamples
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstTermArgumentsRecursiveGroupingSpine
  GrammarAstTermArgumentsRecursiveGroupingExamples
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Distinguish absent arguments, present empty (), and a present refined list.
   The dotted reference and its [Unit] static arguments are retained exactly.
   These fixtures establish grammar structure, not typing or effect semantics. *)

Definition phase1_effect_grouping_example_static_arguments : ParseTree :=
  PTNonterminal "static_arguments"
    (PTSequence
      [PTLiteral "[";
       PTOptionalSome
         (PTSequence
           [PTNonterminal "static_argument"
              (PTAlternative 0
                (PTNonterminal "nonreference_type_expression"
                  (PTAlternative 0 (PTLiteral "Unit"))));
            PTRepetition []]);
       PTLiteral "]"]).

Definition phase1_effect_grouping_example_reference
  : Phase1SurfaceStaticReferenceSpine :=
  {| phase1_static_reference_spine_name :=
       {| phase1_name_list_first := "demo";
          phase1_name_list_rest := ["Emit"] |};
     phase1_static_reference_spine_arguments :=
       Some phase1_effect_grouping_example_static_arguments |}.

Definition phase1_effect_grouping_example_reference_tokens : list ConcreteToken :=
  [TLexical "IDENTIFIER" "demo"; TLiteral ".";
   TLexical "IDENTIFIER" "Emit"; TLiteral "[";
   TLiteral "Unit"; TLiteral "]"].

Definition phase1_effect_grouping_example_tree
  (arguments : option ParseTree) : ParseTree :=
  PTNonterminal "effect_expression"
    (PTSequence
      [phase1_surface_static_reference_spine_tree
         phase1_effect_grouping_example_reference;
       match arguments with
       | None => PTOptionalNone
       | Some tree => PTOptionalSome tree
       end]).

(* Ordinary grammar derivations have no path-dependent side conditions. This
   local helper reuses the already checked term-argument fixtures at their new
   child path; it makes no claim about oracle-resolved derivation paths. *)
Lemma phase1_effect_grouping_example_derivation_repath :
  (forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    forall other_path,
      Derives phase1_surface_rules other_path expression input rest tree) /\
  (forall path index expressions input rest trees,
    DerivesSequence phase1_surface_rules path index expressions input rest trees ->
    forall other_path,
      DerivesSequence phase1_surface_rules other_path index expressions
        input rest trees) /\
  (forall path expression input rest trees,
    DerivesRepetition phase1_surface_rules path expression input rest trees ->
    forall other_path,
      DerivesRepetition phase1_surface_rules other_path expression input rest trees).
Proof.
  apply Derivation_mutind; intros; econstructor; eauto.
Qed.

Lemma phase1_effect_grouping_example_empty_arguments_at_path :
  forall path,
    Derives phase1_surface_rules path (ENonterminal "term_arguments")
      [TLiteral "("; TLiteral ")"] []
      (phase1_term_arguments_grouping_example_tree []).
Proof.
  intro path.
  exact (proj1 phase1_effect_grouping_example_derivation_repath
    [] _ _ _ _ phase1_term_arguments_grouping_empty_fixture_is_grammar_derived path).
Qed.

Lemma phase1_effect_grouping_example_mixed_arguments_at_path :
  forall path,
    Derives phase1_surface_rules path (ENonterminal "term_arguments")
      (phase1_grouping_example_tokens phase1_term_arguments_grouping_example_mixed)
      [] phase1_term_arguments_grouping_example_mixed.
Proof.
  intro path.
  exact (proj1 phase1_effect_grouping_example_derivation_repath
    [] _ _ _ _ phase1_term_arguments_grouping_mixed_fixture_is_grammar_derived path).
Qed.

Ltac phase1_effect_grouping_example_derive_shell :=
  unfold phase1_effect_grouping_example_tree,
    phase1_effect_grouping_example_reference_tokens,
    phase1_surface_static_reference_spine_tree,
    phase1_effect_grouping_example_reference,
    phase1_surface_qualified_name_tree,
    phase1_surface_name_list_tree,
    phase1_surface_identifier_tree,
    phase1_surface_optional_static_arguments_tree,
    phase1_effect_grouping_example_static_arguments;
  cbn [List.app map phase1_static_reference_spine_name
    phase1_static_reference_spine_arguments phase1_name_list_first
    phase1_name_list_rest];
  repeat first
    [ match goal with
      | |- Derives _ _ (ENonterminal "term_arguments") _ _ _ =>
          first
            [ apply phase1_effect_grouping_example_empty_arguments_at_path
            | apply phase1_effect_grouping_example_mixed_arguments_at_path ]
      | |- lookupRule _ _ = _ => vm_compute; reflexivity
      | |- nth_error _ _ = _ => reflexivity
      end
    | econstructor
    | discriminate ].

Example phase1_effect_grouping_absent_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "effect_expression")
    phase1_effect_grouping_example_reference_tokens []
    (phase1_effect_grouping_example_tree None).
Proof. phase1_effect_grouping_example_derive_shell. Qed.

Example phase1_effect_grouping_empty_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "effect_expression")
    (List.app phase1_effect_grouping_example_reference_tokens
      [TLiteral "("; TLiteral ")"]) []
    (phase1_effect_grouping_example_tree
      (Some (phase1_term_arguments_grouping_example_tree []))).
Proof. phase1_effect_grouping_example_derive_shell. Qed.

Example phase1_effect_grouping_mixed_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "effect_expression")
    (List.app phase1_effect_grouping_example_reference_tokens
      (phase1_grouping_example_tokens phase1_term_arguments_grouping_example_mixed))
    [] (phase1_effect_grouping_example_tree
      (Some phase1_term_arguments_grouping_example_mixed)).
Proof. phase1_effect_grouping_example_derive_shell. Qed.

Example phase1_effect_grouping_preserves_absent_arguments :
  phase1_surface_normalize_effect_expression_recursive_grouping_tree
    (phase1_effect_grouping_example_tree None) =
  Some {| phase1_effect_expression_recursive_grouping_spine_reference :=
            phase1_effect_grouping_example_reference;
          phase1_effect_expression_recursive_grouping_spine_arguments := None |}.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_grouping_preserves_present_empty_arguments :
  phase1_surface_normalize_effect_expression_recursive_grouping_tree
    (phase1_effect_grouping_example_tree
      (Some (phase1_term_arguments_grouping_example_tree []))) =
  Some {| phase1_effect_expression_recursive_grouping_spine_reference :=
            phase1_effect_grouping_example_reference;
          phase1_effect_expression_recursive_grouping_spine_arguments :=
            Some {| phase1_term_arguments_recursive_grouping_spine_arguments := [] |} |}.
Proof. vm_compute. reflexivity. Qed.

Definition phase1_effect_grouping_has_complete_present_arguments
  (effect : Phase1SurfaceEffectExpressionRecursiveGroupingSpine) : Prop :=
  phase1_effect_expression_recursive_grouping_spine_reference effect =
    phase1_effect_grouping_example_reference /\
  match phase1_effect_expression_recursive_grouping_spine_arguments effect with
  | Some arguments => phase1_term_arguments_grouping_has_all_refined_values arguments
  | None => False
  end.

Example phase1_effect_grouping_refines_all_present_arguments_and_retains_reference :
  match phase1_surface_normalize_effect_expression_recursive_grouping_tree
    (phase1_effect_grouping_example_tree
      (Some phase1_term_arguments_grouping_example_mixed)) with
  | Some effect => phase1_effect_grouping_has_complete_present_arguments effect
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_effect_grouping_reconstructs_the_complete_tree :
  match phase1_surface_normalize_effect_expression_recursive_grouping_tree
    (phase1_effect_grouping_example_tree
      (Some phase1_term_arguments_grouping_example_mixed)) with
  | Some effect =>
      phase1_surface_effect_expression_recursive_grouping_spine_tree effect =
        phase1_effect_grouping_example_tree
          (Some phase1_term_arguments_grouping_example_mixed)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_grouping_legacy_adapter_preserves_absence :
  phase1_surface_refine_effect_expression_recursive_grouping
    {| phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference :=
         phase1_effect_grouping_example_reference;
       phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments :=
         None |} =
  Some {| phase1_effect_expression_recursive_grouping_spine_reference :=
            phase1_effect_grouping_example_reference;
          phase1_effect_expression_recursive_grouping_spine_arguments := None |}.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_grouping_legacy_adapter_preserves_present_empty_arguments :
  phase1_surface_refine_effect_expression_recursive_grouping
    {| phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference :=
         phase1_effect_grouping_example_reference;
       phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments :=
         Some
           {| phase1_term_arguments_expression_fallback_base_choice_shift_refined_spine_arguments :=
                [] |} |} =
  Some {| phase1_effect_expression_recursive_grouping_spine_reference :=
            phase1_effect_grouping_example_reference;
          phase1_effect_expression_recursive_grouping_spine_arguments :=
            Some {| phase1_term_arguments_recursive_grouping_spine_arguments := [] |} |}.
Proof. vm_compute. reflexivity. Qed.

(* Node-count fuel is only a concrete compatibility input to the old decoder;
   the new raw normalizer and legacy adapter have no fuel argument. *)
Example phase1_effect_grouping_legacy_adapter_refines_the_present_list :
  match
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel
      (phase1_surface_grouping_tree_size
        (phase1_effect_grouping_example_tree
          (Some phase1_term_arguments_grouping_example_mixed)))
      (phase1_effect_grouping_example_tree
        (Some phase1_term_arguments_grouping_example_mixed))
  with
  | Some previous =>
      match phase1_surface_refine_effect_expression_recursive_grouping previous with
      | Some effect =>
          phase1_effect_grouping_has_complete_present_arguments effect /\
          phase1_surface_effect_expression_recursive_grouping_spine_tree effect =
            phase1_effect_grouping_example_tree
              (Some phase1_term_arguments_grouping_example_mixed)
      | None => False
      end
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_effect_grouping_rejects_a_malformed_later_reject_operand :
  phase1_surface_normalize_effect_expression_recursive_grouping_tree
    (phase1_effect_grouping_example_tree
      (Some (phase1_term_arguments_grouping_example_tree
        [phase1_term_arguments_grouping_example_first;
         phase1_expression_grouping_example_command_fail_fixture;
         phase1_expression_grouping_example_expression
           (phase1_expression_grouping_example_shift_base
             phase1_expression_grouping_example_reject_shift)
           (Some (phase1_expression_grouping_example_reject
             (phase1_expression_grouping_example_shift_base
               phase1_expression_grouping_example_bad_shift)))]))) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_grouping_rejects_an_unwrapped_argument_list :
  phase1_surface_normalize_effect_expression_recursive_grouping_tree
    (PTNonterminal "effect_expression"
      (PTSequence
        [phase1_surface_static_reference_spine_tree
           phase1_effect_grouping_example_reference;
         phase1_term_arguments_grouping_example_tree []])) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_grouping_rejects_a_wrong_present_node :
  phase1_surface_normalize_effect_expression_recursive_grouping_tree
    (phase1_effect_grouping_example_tree
      (Some phase1_effect_grouping_example_static_arguments)) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_grouping_rejects_malformed_present_parentheses :
  phase1_surface_normalize_effect_expression_recursive_grouping_tree
    (phase1_effect_grouping_example_tree
      (Some (PTNonterminal "term_arguments"
        (PTSequence [PTLiteral "("; PTOptionalNone; PTLiteral "]"])))) = None.
Proof. vm_compute. reflexivity. Qed.
