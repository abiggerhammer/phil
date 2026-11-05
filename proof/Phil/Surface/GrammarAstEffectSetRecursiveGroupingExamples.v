From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstSourceHeader
  GrammarAstStaticReferenceSpine
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingTotality
  GrammarAstRecursiveGroupingExamples
  GrammarAstExpressionRecursiveGroupingExamples
  GrammarAstTermArgumentsRecursiveGroupingSpine
  GrammarAstTermArgumentsRecursiveGroupingExamples
  GrammarAstEffectExpressionRecursiveGroupingSpine
  GrammarAstEffectExpressionRecursiveGroupingExamples
  GrammarAstEffectSetExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectSetRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Refine every ordered literal member and preserve the literal/reference
   alternative. Empty {} is distinct from a member with absent or empty term
   arguments. Fixtures establish grammar structure, not effect semantics. *)

Definition phase1_effect_set_grouping_example_literal
  (effects : list ParseTree) : ParseTree :=
  PTNonterminal "effect_set_literal"
    (PTSequence
      [PTLiteral "{";
       match effects with
       | [] => PTOptionalNone
       | first :: rest =>
           PTOptionalSome
             (PTSequence
               [first;
                PTRepetition
                  (map (fun effect => PTSequence [PTLiteral ","; effect]) rest)])
       end;
       PTLiteral "}"]).

Definition phase1_effect_set_grouping_example_values : list ParseTree :=
  [phase1_effect_grouping_example_tree None;
   phase1_effect_grouping_example_tree
     (Some (phase1_term_arguments_grouping_example_tree []));
   phase1_effect_grouping_example_tree
     (Some phase1_term_arguments_grouping_example_mixed)].

Definition phase1_effect_set_grouping_example_mixed_literal : ParseTree :=
  phase1_effect_set_grouping_example_literal phase1_effect_set_grouping_example_values.

Definition phase1_effect_set_grouping_example_literal_choice
  (literal : ParseTree) : ParseTree :=
  PTNonterminal "effect_set_expression" (PTAlternative 0 literal).

Definition phase1_effect_set_grouping_example_reference_choice : ParseTree :=
  PTNonterminal "effect_set_expression"
    (PTAlternative 1
      (phase1_surface_static_reference_spine_tree
        phase1_effect_grouping_example_reference)).

Definition phase1_effect_set_grouping_example_mixed_tokens : list ConcreteToken :=
  TLiteral "{" ::
    List.app phase1_effect_grouping_example_reference_tokens
      (TLiteral "," ::
        List.app
          (List.app phase1_effect_grouping_example_reference_tokens
            [TLiteral "("; TLiteral ")"])
          (TLiteral "," ::
            List.app
              (List.app phase1_effect_grouping_example_reference_tokens
                (phase1_grouping_example_tokens
                  phase1_term_arguments_grouping_example_mixed))
              [TLiteral "}"])).

(* Ordinary grammar derivations can retain an additional unconsumed token
   suffix. Repetition progress is preserved by right cancellation of append.
   This is not a path/lookahead invariance claim about oracle-resolved parsing. *)
Lemma phase1_effect_set_grouping_example_derivation_suffix :
  (forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    forall suffix,
      Derives phase1_surface_rules path expression
        (List.app input suffix) (List.app rest suffix) tree) /\
  (forall path index expressions input rest trees,
    DerivesSequence phase1_surface_rules path index expressions input rest trees ->
    forall suffix,
      DerivesSequence phase1_surface_rules path index expressions
        (List.app input suffix) (List.app rest suffix) trees) /\
  (forall path expression input rest trees,
    DerivesRepetition phase1_surface_rules path expression input rest trees ->
    forall suffix,
      DerivesRepetition phase1_surface_rules path expression
        (List.app input suffix) (List.app rest suffix) trees).
Proof.
  apply Derivation_mutind; intros; cbn [List.app]; econstructor; eauto.
  intro Hsame. apply app_inv_tail in Hsame. contradiction.
Qed.

Lemma phase1_effect_set_grouping_example_in_context :
  forall path expression input tree,
    Derives phase1_surface_rules [] expression input [] tree ->
    forall suffix,
      Derives phase1_surface_rules path expression
        (List.app input suffix) suffix tree.
Proof.
  intros path expression input tree Hderive suffix.
  pose proof
    (proj1 phase1_effect_grouping_example_derivation_repath
      [] expression input [] tree Hderive path) as Hpath.
  exact
    (proj1 phase1_effect_set_grouping_example_derivation_suffix
      path expression input [] tree Hpath suffix).
Qed.

Example phase1_effect_set_grouping_empty_literal_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "effect_set_literal")
    [TLiteral "{"; TLiteral "}"] []
    (phase1_effect_set_grouping_example_literal []).
Proof.
  unfold phase1_effect_set_grouping_example_literal.
  repeat first
    [ match goal with
      | |- lookupRule _ _ = _ => vm_compute; reflexivity
      | |- nth_error _ _ = _ => reflexivity
      end
    | econstructor
    | discriminate ].
Qed.

Example phase1_effect_set_grouping_mixed_literal_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "effect_set_literal")
    phase1_effect_set_grouping_example_mixed_tokens []
    phase1_effect_set_grouping_example_mixed_literal.
Proof.
  unfold phase1_effect_set_grouping_example_mixed_literal,
    phase1_effect_set_grouping_example_literal,
    phase1_effect_set_grouping_example_values,
    phase1_effect_set_grouping_example_mixed_tokens.
  cbn [map].
  repeat first
    [ match goal with
      | |- Derives _ ?path (ENonterminal "effect_expression") _ ?rest _ =>
          first
            [ exact (phase1_effect_set_grouping_example_in_context path _ _ _
                phase1_effect_grouping_absent_fixture_is_grammar_derived rest)
            | exact (phase1_effect_set_grouping_example_in_context path _ _ _
                phase1_effect_grouping_empty_fixture_is_grammar_derived rest)
            | exact (phase1_effect_set_grouping_example_in_context path _ _ _
                phase1_effect_grouping_mixed_fixture_is_grammar_derived rest) ]
      | |- lookupRule _ _ = _ => vm_compute; reflexivity
      | |- nth_error _ _ = _ => reflexivity
      end
    | econstructor
    | discriminate ].
Qed.

Example phase1_effect_set_grouping_literal_choice_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "effect_set_expression")
    phase1_effect_set_grouping_example_mixed_tokens []
    (phase1_effect_set_grouping_example_literal_choice
      phase1_effect_set_grouping_example_mixed_literal).
Proof.
  unfold phase1_effect_set_grouping_example_literal_choice.
  repeat first
    [ match goal with
      | |- Derives _ ?path (ENonterminal "effect_set_literal") _ _ _ =>
          exact (proj1 phase1_effect_grouping_example_derivation_repath
            [] _ _ _ _ phase1_effect_set_grouping_mixed_literal_is_grammar_derived path)
      | |- lookupRule _ _ = _ => vm_compute; reflexivity
      | |- nth_error _ _ = _ => reflexivity
      end
    | econstructor
    | discriminate ].
Qed.

Example phase1_effect_set_grouping_reference_choice_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "effect_set_expression")
    phase1_effect_grouping_example_reference_tokens []
    phase1_effect_set_grouping_example_reference_choice.
Proof.
  unfold phase1_effect_set_grouping_example_reference_choice,
    phase1_effect_grouping_example_reference_tokens,
    phase1_surface_static_reference_spine_tree,
    phase1_effect_grouping_example_reference,
    phase1_surface_qualified_name_tree,
    phase1_surface_name_list_tree,
    phase1_surface_identifier_tree,
    phase1_surface_optional_static_arguments_tree,
    phase1_effect_grouping_example_static_arguments.
  cbn [map phase1_static_reference_spine_name
    phase1_static_reference_spine_arguments phase1_name_list_first
    phase1_name_list_rest].
  repeat first
    [ match goal with
      | |- lookupRule _ _ = _ => vm_compute; reflexivity
      | |- nth_error _ _ = _ => reflexivity
      end
    | econstructor
    | discriminate ].
Qed.

Example phase1_effect_set_grouping_preserves_empty_braces :
  phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
    (phase1_effect_set_grouping_example_literal []) =
  Some {| phase1_effect_set_literal_recursive_grouping_spine_effects := [] |}.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_set_grouping_preserves_a_single_complete_member :
  match phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
    (phase1_effect_set_grouping_example_literal
      [phase1_effect_grouping_example_tree
        (Some phase1_term_arguments_grouping_example_mixed)]) with
  | Some literal =>
      match phase1_effect_set_literal_recursive_grouping_spine_effects literal with
      | [effect] => phase1_effect_grouping_has_complete_present_arguments effect
      | _ => False
      end
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition phase1_effect_set_grouping_has_all_members
  (literal : Phase1SurfaceEffectSetLiteralRecursiveGroupingSpine) : Prop :=
  match phase1_effect_set_literal_recursive_grouping_spine_effects literal with
  | [absent; empty; present] =>
      absent =
        {| phase1_effect_expression_recursive_grouping_spine_reference :=
             phase1_effect_grouping_example_reference;
           phase1_effect_expression_recursive_grouping_spine_arguments := None |} /\
      empty =
        {| phase1_effect_expression_recursive_grouping_spine_reference :=
             phase1_effect_grouping_example_reference;
           phase1_effect_expression_recursive_grouping_spine_arguments :=
             Some {| phase1_term_arguments_recursive_grouping_spine_arguments := [] |} |} /\
      phase1_effect_grouping_has_complete_present_arguments present
  | _ => False
  end.

Example phase1_effect_set_grouping_refines_every_member_in_order :
  match phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
    phase1_effect_set_grouping_example_mixed_literal with
  | Some literal => phase1_effect_set_grouping_has_all_members literal
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_effect_set_grouping_preserves_the_complete_effect_list :
  match phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
    phase1_effect_set_grouping_example_mixed_literal with
  | Some literal =>
      map phase1_surface_effect_expression_recursive_grouping_spine_tree
        (phase1_effect_set_literal_recursive_grouping_spine_effects literal) =
        phase1_effect_set_grouping_example_values
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_set_grouping_preserves_literal_choice_and_complete_tree :
  match phase1_surface_normalize_effect_set_recursive_grouping_tree
    (phase1_effect_set_grouping_example_literal_choice
      phase1_effect_set_grouping_example_mixed_literal) with
  | Some (Phase1EffectSetGroupingLiteral literal) =>
      phase1_effect_set_grouping_has_all_members literal /\
      phase1_surface_effect_set_recursive_grouping_spine_tree
        (Phase1EffectSetGroupingLiteral literal) =
        phase1_effect_set_grouping_example_literal_choice
          phase1_effect_set_grouping_example_mixed_literal
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_effect_set_grouping_preserves_the_reference_choice :
  phase1_surface_normalize_effect_set_recursive_grouping_tree
    phase1_effect_set_grouping_example_reference_choice =
  Some (Phase1EffectSetGroupingReference phase1_effect_grouping_example_reference).
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_set_grouping_legacy_adapter_preserves_empty_literal :
  phase1_surface_refine_effect_set_literal_recursive_grouping
    {| phase1_effect_set_expression_fallback_base_choice_shift_refined_literal_spine_effects :=
         [] |} =
  Some {| phase1_effect_set_literal_recursive_grouping_spine_effects := [] |}.
Proof. vm_compute. reflexivity. Qed.

(* Node-count fuel is a concrete input to the old decoder, not a universal
   bound for it. Both new legacy adapters have no fuel parameter. *)
Example phase1_effect_set_grouping_legacy_adapters_replace_every_literal_member :
  match
    phase1_surface_normalize_effect_set_expression_fallback_base_choice_shift_refined_tree_fuel
      (phase1_surface_grouping_tree_size
        (phase1_effect_set_grouping_example_literal_choice
          phase1_effect_set_grouping_example_mixed_literal))
      (phase1_effect_set_grouping_example_literal_choice
        phase1_effect_set_grouping_example_mixed_literal)
  with
  | Some (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedLiteral previous) =>
      match phase1_surface_refine_effect_set_literal_recursive_grouping previous,
        phase1_surface_refine_effect_set_recursive_grouping
          (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedLiteral previous)
      with
      | Some literal, Some (Phase1EffectSetGroupingLiteral selected) =>
          phase1_effect_set_grouping_has_all_members literal /\
          selected = literal /\
          phase1_surface_effect_set_recursive_grouping_spine_tree
            (Phase1EffectSetGroupingLiteral selected) =
            phase1_effect_set_grouping_example_literal_choice
              phase1_effect_set_grouping_example_mixed_literal
      | _, _ => False
      end
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_effect_set_grouping_legacy_adapter_preserves_reference :
  phase1_surface_refine_effect_set_recursive_grouping
    (Phase1EffectSetExpressionFallbackBaseChoiceShiftRefinedReference
      phase1_effect_grouping_example_reference) =
  Some (Phase1EffectSetGroupingReference phase1_effect_grouping_example_reference).
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_set_grouping_rejects_a_later_malformed_reject_operand :
  phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
    (phase1_effect_set_grouping_example_literal
      [phase1_effect_grouping_example_tree None;
       phase1_effect_grouping_example_tree
         (Some (phase1_term_arguments_grouping_example_tree []));
       phase1_effect_grouping_example_tree
         (Some (phase1_term_arguments_grouping_example_tree
           [phase1_term_arguments_grouping_example_first;
            phase1_expression_grouping_example_command_fail_fixture;
            phase1_expression_grouping_example_expression
              (phase1_expression_grouping_example_shift_base
                phase1_expression_grouping_example_reject_shift)
              (Some (phase1_expression_grouping_example_reject
                (phase1_expression_grouping_example_shift_base
                  phase1_expression_grouping_example_bad_shift)))]))]) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_set_grouping_rejects_a_wrong_separator :
  phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
    (PTNonterminal "effect_set_literal"
      (PTSequence
        [PTLiteral "{";
         PTOptionalSome
           (PTSequence
             [phase1_effect_grouping_example_tree None;
              PTRepetition
                [PTSequence [PTLiteral ";";
                  phase1_effect_grouping_example_tree
                    (Some (phase1_term_arguments_grouping_example_tree []))]]]);
         PTLiteral "}"])) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_set_grouping_rejects_a_trailing_comma :
  phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
    (PTNonterminal "effect_set_literal"
      (PTSequence
        [PTLiteral "{";
         PTOptionalSome
           (PTSequence
             [phase1_effect_grouping_example_tree None;
              PTRepetition [PTSequence [PTLiteral ","]]]);
         PTLiteral "}"])) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_set_grouping_rejects_a_wrong_closing_delimiter :
  phase1_surface_normalize_effect_set_literal_recursive_grouping_tree
    (PTNonterminal "effect_set_literal"
      (PTSequence [PTLiteral "{"; PTOptionalNone; PTLiteral "]"])) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_set_grouping_rejects_an_unknown_choice_index :
  phase1_surface_normalize_effect_set_recursive_grouping_tree
    (PTNonterminal "effect_set_expression"
      (PTAlternative 2 (phase1_effect_set_grouping_example_literal []))) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_effect_set_grouping_rejects_a_mismatched_choice :
  phase1_surface_normalize_effect_set_recursive_grouping_tree
    (PTNonterminal "effect_set_expression"
      (PTAlternative 1 (phase1_effect_set_grouping_example_literal []))) = None.
Proof. vm_compute. reflexivity. Qed.
