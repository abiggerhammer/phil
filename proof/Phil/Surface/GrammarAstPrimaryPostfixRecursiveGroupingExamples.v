From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstSourceHeader
  GrammarAstStaticArgumentsSpine
  GrammarAstTermArgumentsSpine
  GrammarAstNamedPostfixTermProjectionSpine
  GrammarAstNamedPostfixExpressionRefinedTailSpine
  GrammarAstPostfixExpressionRefinedSpine
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingTotality
  GrammarAstRecursiveGroupingExamples
  GrammarAstPrimaryExpressionLiteralSpine
  GrammarAstPrimaryExpressionCharSpine
  GrammarAstPrimaryExpressionStringSpine
  GrammarAstPrimaryExpressionFloatSpine
  GrammarAstPrimaryExpressionIntegerSpine
  GrammarAstPrimaryExpressionRecursiveGroupingSpine
  GrammarAstPostfixExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001: these controls inspect the replacement
   primary payload and its immediate postfix consumer. The universal
   derivation-driven totality theorems remain the main evidence. Lexical
   spellings are preserved as token payloads, without numeric interpretation. *)

Definition phase1_primary_grouping_example_leaf
  (branch : nat) (selected : ParseTree) : ParseTree :=
  PTNonterminal "primary_expression" (PTAlternative branch selected).

Definition phase1_primary_grouping_example_literals
  : list (ParseTree * Phase1SurfacePrimaryExpressionRecursiveGroupingSpine) :=
  [ (phase1_primary_grouping_example_leaf 2 (PTLiteral "true"),
       Phase1PrimaryGroupingTrue);
    (phase1_primary_grouping_example_leaf 3 (PTLiteral "false"),
       Phase1PrimaryGroupingFalse);
    (phase1_primary_grouping_example_leaf 4 (PTLiteral "unit"),
       Phase1PrimaryGroupingUnit);
    (phase1_primary_grouping_example_leaf 5
       (PTNonterminal "char_literal" (PTLexical "CHAR_LITERAL" "'a'")),
       Phase1PrimaryGroupingChar "'a'");
    (phase1_primary_grouping_example_leaf 6
       (PTNonterminal "runtime_string_literal"
         (PTLexical "STRING_LITERAL" """hello""")),
       Phase1PrimaryGroupingString """hello""");
    (phase1_primary_grouping_example_leaf 7
       (PTNonterminal "float_literal" (PTLexical "DECIMAL_FLOAT" "1.250e+02")),
       Phase1PrimaryGroupingFloat "1.250e+02");
    (phase1_primary_grouping_example_leaf 8
       (PTNonterminal "integer_literal" (PTLexical "DECIMAL_INTEGER" "42")),
       Phase1PrimaryGroupingInteger "42") ].

Example phase1_primary_grouping_preserves_all_literal_choices_and_spellings :
  Forall
    (fun item =>
       phase1_surface_normalize_primary_expression_recursive_grouping_tree
         (fst item) = Some (snd item))
    phase1_primary_grouping_example_literals.
Proof. vm_compute. repeat constructor. Qed.

Definition phase1_primary_grouping_example_tuple : ParseTree :=
  phase1_primary_grouping_example_leaf 0
    (PTNonterminal "tuple_expression"
      (PTSequence
        [ PTLiteral "(";
          phase1_grouping_example_parenthesized
            (phase1_grouping_example_integer "1");
          PTLiteral ",";
          phase1_grouping_example_tuple
            (phase1_grouping_example_integer "2")
            (phase1_grouping_example_parenthesized
              (phase1_grouping_example_integer "3")) [];
          PTRepetition
            [PTSequence
              [ PTLiteral ",";
                phase1_grouping_example_parenthesized
                  (phase1_grouping_example_integer "4") ]];
          PTLiteral ")" ])).

Definition phase1_primary_grouping_example_parenthesized : ParseTree :=
  phase1_primary_grouping_example_leaf 1
    (PTNonterminal "parenthesized_expression"
      (PTSequence
        [PTLiteral "("; phase1_grouping_example_nested; PTLiteral ")"])).

Example phase1_primary_grouping_tuple_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "primary_expression")
    (phase1_grouping_example_tokens phase1_primary_grouping_example_tuple) []
    phase1_primary_grouping_example_tuple.
Proof.
  unfold phase1_primary_grouping_example_tuple,
    phase1_primary_grouping_example_leaf,
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

Example phase1_primary_grouping_tuple_replaces_every_child :
  match phase1_surface_normalize_primary_expression_recursive_grouping_tree
    phase1_primary_grouping_example_tuple with
  | Some (Phase1PrimaryGroupingTuple first second [last]) =>
      phase1_grouping_example_expression_count first = 1 /\
      phase1_grouping_example_expression_count second = 2 /\
      phase1_grouping_example_expression_count last = 1
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_primary_grouping_parenthesized_child_is_recursive :
  match phase1_surface_normalize_primary_expression_recursive_grouping_tree
    phase1_primary_grouping_example_parenthesized with
  | Some (Phase1PrimaryGroupingParenthesized expression) =>
      phase1_grouping_example_expression_count expression = 6
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_primary_grouping_tuple_reconstruction_is_exact :
  match phase1_surface_normalize_primary_expression_recursive_grouping_tree
    phase1_primary_grouping_example_tuple with
  | Some refined =>
      phase1_surface_primary_expression_recursive_grouping_spine_tree refined =
        phase1_primary_grouping_example_tuple
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Definition phase1_primary_grouping_example_legacy_retained
  (branch : nat) (selected : ParseTree)
  : Phase1SurfacePrimaryExpressionIntegerSpine :=
  Phase1PrimaryExpressionIntegerPrior
    (Phase1PrimaryExpressionFloatPrior
      (Phase1PrimaryExpressionStringPrior
        (Phase1PrimaryExpressionCharPrior
          (Phase1PrimaryExpressionLexicalRetained branch selected)))).

(* An old carrier can have a valid erasure even when its inhabitant was not
   itself produced by the old normalizer. Canonicalizing its tree must still
   satisfy the adapter's derivation-only domain. *)
Example phase1_primary_grouping_canonicalizes_legacy_retained_integer :
  phase1_surface_refine_primary_expression_recursive_grouping
    (phase1_primary_grouping_example_legacy_retained 8
      (PTNonterminal "integer_literal" (PTLexical "DECIMAL_INTEGER" "42"))) =
    Some (Phase1PrimaryGroupingInteger "42").
Proof. vm_compute. reflexivity. Qed.

Example phase1_primary_grouping_canonicalizes_legacy_retained_group :
  match phase1_surface_refine_primary_expression_recursive_grouping
    (phase1_primary_grouping_example_legacy_retained 1
      (PTNonterminal "parenthesized_expression"
        (PTSequence
          [PTLiteral "("; phase1_grouping_example_nested; PTLiteral ")"]))) with
  | Some (Phase1PrimaryGroupingParenthesized expression) =>
      phase1_grouping_example_expression_count expression = 6
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example phase1_primary_grouping_rejects_unknown_branch :
  phase1_surface_normalize_primary_expression_recursive_grouping_tree
    (phase1_primary_grouping_example_leaf 9 (PTLiteral "true")) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_primary_grouping_rejects_wrong_lexical_class :
  phase1_surface_normalize_primary_expression_recursive_grouping_tree
    (phase1_primary_grouping_example_leaf 8
      (PTNonterminal "integer_literal" (PTLexical "DECIMAL_FLOAT" "42"))) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_primary_grouping_rejects_malformed_nested_group :
  phase1_surface_normalize_primary_expression_recursive_grouping_tree
    (phase1_primary_grouping_example_leaf 1
      phase1_grouping_example_malformed) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_primary_grouping_rejects_tuple_without_second_element :
  phase1_surface_normalize_primary_expression_recursive_grouping_tree
    (phase1_primary_grouping_example_leaf 0
      (PTNonterminal "tuple_expression"
        (PTSequence
          [PTLiteral "("; phase1_grouping_example_integer "1";
           PTRepetition []; PTLiteral ")"]))) = None.
Proof. vm_compute. reflexivity. Qed.

Definition phase1_postfix_grouping_example_projection
  (name : string) : ParseTree :=
  PTSequence
    [PTLiteral "."; PTNonterminal "identifier" (PTLexical "IDENTIFIER" name)].

Definition phase1_postfix_grouping_example_tuple_projections : ParseTree :=
  PTNonterminal "postfix_expression"
    (PTAlternative 1
      (PTSequence
        [ phase1_primary_grouping_example_tuple;
          PTRepetition
            [phase1_postfix_grouping_example_projection "first";
             phase1_postfix_grouping_example_projection "rest"] ])).

Example phase1_postfix_grouping_projected_fixture_is_grammar_derived :
  Derives phase1_surface_rules [] (ENonterminal "postfix_expression")
    (phase1_grouping_example_tokens
      phase1_postfix_grouping_example_tuple_projections) []
    phase1_postfix_grouping_example_tuple_projections.
Proof.
  unfold phase1_postfix_grouping_example_tuple_projections,
    phase1_postfix_grouping_example_projection,
    phase1_primary_grouping_example_tuple,
    phase1_primary_grouping_example_leaf,
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

Example phase1_postfix_grouping_consumes_recursive_primary_and_keeps_projection_order :
  match phase1_surface_normalize_postfix_expression_recursive_grouping_tree
    phase1_postfix_grouping_example_tuple_projections with
  | Some (Phase1PostfixGroupingPrimary
      (Phase1PrimaryGroupingTuple first second [last]) projections) =>
      phase1_grouping_example_expression_count first = 1 /\
      phase1_grouping_example_expression_count second = 2 /\
      phase1_grouping_example_expression_count last = 1 /\
      projections = ["first"; "rest"]
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example phase1_postfix_grouping_projected_reconstruction_is_exact :
  match phase1_surface_normalize_postfix_expression_recursive_grouping_tree
    phase1_postfix_grouping_example_tuple_projections with
  | Some refined =>
      phase1_surface_postfix_expression_recursive_grouping_spine_tree refined =
        phase1_postfix_grouping_example_tuple_projections
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Definition phase1_postfix_grouping_example_named
  (tail : option Phase1SurfaceNamedPostfixTermProjectionSpine)
  : Phase1SurfaceNamedPostfixExpressionRefinedTailSpine :=
  {| phase1_named_postfix_expression_refined_tail_name :=
       {| phase1_name_list_first := "Math";
          phase1_name_list_rest := ["combine"] |};
     phase1_named_postfix_expression_refined_tail := tail |}.

Definition phase1_postfix_grouping_example_named_tails
  : list (option Phase1SurfaceNamedPostfixTermProjectionSpine) :=
  [ None;
    Some (Phase1NamedPostfixTermProjectionRefined
      {| phase1_term_arguments_spine_arguments :=
           [phase1_grouping_example_nested] |} ["head"; "leaf"]);
    Some (Phase1NamedPostfixStaticRetainedAfterTermProjection
      {| phase1_static_arguments_spine_items := None |} None ["head"]);
    Some (Phase1NamedPostfixStaticRetainedAfterTermProjection
      {| phase1_static_arguments_spine_items := None |}
      (Some {| phase1_term_arguments_spine_arguments :=
                 [phase1_grouping_example_nested] |}) ["head"; "leaf"]) ].

Example phase1_postfix_grouping_preserves_all_existing_named_tail_choices :
  Forall
    (fun tail =>
      phase1_surface_normalize_postfix_expression_recursive_grouping_tree
        (PTNonterminal "postfix_expression"
          (PTAlternative 0
            (phase1_surface_named_postfix_expression_refined_tail_spine_tree
              (phase1_postfix_grouping_example_named tail)))) =
      Some (Phase1PostfixGroupingNamed
        (phase1_postfix_grouping_example_named tail)))
    phase1_postfix_grouping_example_named_tails.
Proof. vm_compute. repeat constructor. Qed.

Example phase1_postfix_grouping_legacy_named_adapter_preserves_payload :
  forall named,
    phase1_surface_refine_postfix_expression_recursive_grouping
      (Phase1SurfacePostfixExpressionNamedFullyRefined named) =
    Some (Phase1PostfixGroupingNamed named).
Proof. reflexivity. Qed.

Example phase1_postfix_grouping_legacy_primary_adapter_replaces_payload :
  match phase1_surface_refine_postfix_expression_recursive_grouping
    (Phase1SurfacePostfixExpressionPrimaryRefined
      (phase1_primary_grouping_example_legacy_retained 1
        (PTNonterminal "parenthesized_expression"
          (PTSequence
            [PTLiteral "("; phase1_grouping_example_nested; PTLiteral ")"])))
      ["head"; "leaf"]) with
  | Some (Phase1PostfixGroupingPrimary
      (Phase1PrimaryGroupingParenthesized expression) projections) =>
      phase1_grouping_example_expression_count expression = 6 /\
      projections = ["head"; "leaf"]
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example phase1_postfix_grouping_rejects_malformed_primary :
  phase1_surface_normalize_postfix_expression_recursive_grouping_tree
    (PTNonterminal "postfix_expression"
      (PTAlternative 1
        (PTSequence
          [phase1_primary_grouping_example_leaf 1
             phase1_grouping_example_malformed;
           PTRepetition []]))) = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_postfix_grouping_rejects_malformed_projection :
  phase1_surface_normalize_postfix_expression_recursive_grouping_tree
    (PTNonterminal "postfix_expression"
      (PTAlternative 1
        (PTSequence
          [phase1_primary_grouping_example_tuple;
           PTRepetition [PTLiteral "head"]]))) = None.
Proof. vm_compute. reflexivity. Qed.
