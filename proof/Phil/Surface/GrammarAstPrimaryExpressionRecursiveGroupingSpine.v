From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingTotality
  GrammarAstPrimaryExpressionIntegerSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Replace the two recursive ParseTree payloads in the completed primary
   expression carrier. The seven keyword/lexical alternatives retain their
   existing exact representation. No predecessor carrier or redundant source
   tree is stored alongside the new value. *)
Inductive Phase1SurfacePrimaryExpressionRecursiveGroupingSpine : Type :=
| Phase1PrimaryGroupingTuple
    (first second : Phase1SurfaceRecursiveGroupingExpression)
    (rest : list Phase1SurfaceRecursiveGroupingExpression)
| Phase1PrimaryGroupingParenthesized
    (expression : Phase1SurfaceRecursiveGroupingExpression)
| Phase1PrimaryGroupingTrue
| Phase1PrimaryGroupingFalse
| Phase1PrimaryGroupingUnit
| Phase1PrimaryGroupingChar (value : string)
| Phase1PrimaryGroupingString (value : string)
| Phase1PrimaryGroupingFloat (value : string)
| Phase1PrimaryGroupingInteger (value : string).

Definition phase1_surface_primary_expression_recursive_grouping_index
  (expression : Phase1SurfacePrimaryExpressionRecursiveGroupingSpine) : nat :=
  match expression with
  | Phase1PrimaryGroupingTuple _ _ _ => 0
  | Phase1PrimaryGroupingParenthesized _ => 1
  | Phase1PrimaryGroupingTrue => 2
  | Phase1PrimaryGroupingFalse => 3
  | Phase1PrimaryGroupingUnit => 4
  | Phase1PrimaryGroupingChar _ => 5
  | Phase1PrimaryGroupingString _ => 6
  | Phase1PrimaryGroupingFloat _ => 7
  | Phase1PrimaryGroupingInteger _ => 8
  end.

Definition phase1_surface_primary_expression_recursive_grouping_selected_tree
  (expression : Phase1SurfacePrimaryExpressionRecursiveGroupingSpine)
  : ParseTree :=
  match expression with
  | Phase1PrimaryGroupingTuple first second rest =>
      phase1_surface_recursive_grouping_tree
        (Phase1GroupingTuple first second rest)
  | Phase1PrimaryGroupingParenthesized expression =>
      phase1_surface_recursive_grouping_tree
        (Phase1GroupingParenthesized expression)
  | Phase1PrimaryGroupingTrue => PTLiteral "true"
  | Phase1PrimaryGroupingFalse => PTLiteral "false"
  | Phase1PrimaryGroupingUnit => PTLiteral "unit"
  | Phase1PrimaryGroupingChar value =>
      PTNonterminal "char_literal" (PTLexical "CHAR_LITERAL" value)
  | Phase1PrimaryGroupingString value =>
      PTNonterminal "runtime_string_literal" (PTLexical "STRING_LITERAL" value)
  | Phase1PrimaryGroupingFloat value =>
      PTNonterminal "float_literal" (PTLexical "DECIMAL_FLOAT" value)
  | Phase1PrimaryGroupingInteger value =>
      PTNonterminal "integer_literal" (PTLexical "DECIMAL_INTEGER" value)
  end.

Definition phase1_surface_primary_expression_recursive_grouping_spine_tree
  (expression : Phase1SurfacePrimaryExpressionRecursiveGroupingSpine)
  : ParseTree :=
  PTNonterminal "primary_expression"
    (PTAlternative
      (phase1_surface_primary_expression_recursive_grouping_index expression)
      (phase1_surface_primary_expression_recursive_grouping_selected_tree
        expression)).

Definition phase1_surface_grouping_lexical_payload
  (expected_name expected_class : string)
  (tree : Phase1SurfaceRecursiveGroupingTree) : option string :=
  match tree with
  | Phase1GroupingNonterminal name (Phase1GroupingLexical class value) =>
      if String.eqb name expected_name then
        if String.eqb class expected_class then Some value else None
      else None
  | _ => None
  end.

Definition phase1_surface_primary_expression_recursive_grouping_branch
  (index : nat) (selected : Phase1SurfaceRecursiveGroupingTree)
  : option Phase1SurfacePrimaryExpressionRecursiveGroupingSpine :=
  match index with
  | 0 =>
      match selected with
      | Phase1GroupingTuple first second rest =>
          Some (Phase1PrimaryGroupingTuple first second rest)
      | _ => None
      end
  | 1 =>
      match selected with
      | Phase1GroupingParenthesized expression =>
          Some (Phase1PrimaryGroupingParenthesized expression)
      | _ => None
      end
  | 2 =>
      match selected with
      | Phase1GroupingLiteral literal =>
          if String.eqb literal "true" then Some Phase1PrimaryGroupingTrue
          else None
      | _ => None
      end
  | 3 =>
      match selected with
      | Phase1GroupingLiteral literal =>
          if String.eqb literal "false" then Some Phase1PrimaryGroupingFalse
          else None
      | _ => None
      end
  | 4 =>
      match selected with
      | Phase1GroupingLiteral literal =>
          if String.eqb literal "unit" then Some Phase1PrimaryGroupingUnit
          else None
      | _ => None
      end
  | 5 => option_map Phase1PrimaryGroupingChar
      (phase1_surface_grouping_lexical_payload "char_literal" "CHAR_LITERAL"
        selected)
  | 6 => option_map Phase1PrimaryGroupingString
      (phase1_surface_grouping_lexical_payload
        "runtime_string_literal" "STRING_LITERAL" selected)
  | 7 => option_map Phase1PrimaryGroupingFloat
      (phase1_surface_grouping_lexical_payload "float_literal" "DECIMAL_FLOAT"
        selected)
  | 8 => option_map Phase1PrimaryGroupingInteger
      (phase1_surface_grouping_lexical_payload
        "integer_literal" "DECIMAL_INTEGER" selected)
  | _ => None
  end.

Definition phase1_surface_primary_expression_recursive_grouping_from_tree
  (tree : Phase1SurfaceRecursiveGroupingTree)
  : option Phase1SurfacePrimaryExpressionRecursiveGroupingSpine :=
  match tree with
  | Phase1GroupingNonterminal name (Phase1GroupingAlternative index selected) =>
      if String.eqb name "primary_expression" then
        phase1_surface_primary_expression_recursive_grouping_branch index selected
      else None
  | _ => None
  end.

Definition phase1_surface_normalize_primary_expression_recursive_grouping_tree
  (tree : ParseTree)
  : option Phase1SurfacePrimaryExpressionRecursiveGroupingSpine :=
  match phase1_surface_normalize_recursive_grouping tree with
  | Some normalized =>
      phase1_surface_primary_expression_recursive_grouping_from_tree normalized
  | None => None
  end.

Definition phase1_surface_refine_primary_expression_recursive_grouping
  (expression : Phase1SurfacePrimaryExpressionIntegerSpine)
  : option Phase1SurfacePrimaryExpressionRecursiveGroupingSpine :=
  phase1_surface_normalize_primary_expression_recursive_grouping_tree
    (phase1_surface_primary_expression_integer_spine_tree expression).

Lemma phase1_surface_grouping_lexical_payload_round_trip :
  forall expected_name expected_class tree value,
    phase1_surface_grouping_lexical_payload expected_name expected_class tree =
      Some value ->
    phase1_surface_recursive_grouping_tree tree =
      PTNonterminal expected_name (PTLexical expected_class value).
Proof.
  intros expected_name expected_class tree value Hpayload.
  destruct tree as
    [literal |class lexeme |name body |items |index body
    | |body |items |expression |expression |first second rest |body |body];
    try discriminate Hpayload.
  destruct body as
    [literal |class lexeme |inner_name inner_body |items |index inner_body
    | |inner_body |items |expression |expression |first second rest
    |inner_body |inner_body]; try discriminate Hpayload.
  unfold phase1_surface_grouping_lexical_payload in Hpayload.
  destruct (String.eqb name expected_name) eqn:Hname;
    try discriminate Hpayload.
  destruct (String.eqb class expected_class) eqn:Hclass;
    try discriminate Hpayload.
  apply String.eqb_eq in Hname. apply String.eqb_eq in Hclass.
  inversion Hpayload; subst. reflexivity.
Qed.

Lemma phase1_surface_primary_expression_recursive_grouping_branch_round_trip :
  forall index selected expression,
    phase1_surface_primary_expression_recursive_grouping_branch index selected =
      Some expression ->
    phase1_surface_primary_expression_recursive_grouping_spine_tree expression =
      PTNonterminal "primary_expression"
        (PTAlternative index (phase1_surface_recursive_grouping_tree selected)).
Proof.
  intros index selected expression Hnormalize.
  destruct index as [|[|[|[|[|[|[|[|[|index]]]]]]]]].
  - destruct selected; try discriminate Hnormalize.
    inversion Hnormalize; reflexivity.
  - destruct selected; try discriminate Hnormalize.
    inversion Hnormalize; reflexivity.
  - destruct selected; try discriminate Hnormalize.
    cbn in Hnormalize.
    destruct (String.eqb literal "true") eqn:Hliteral;
      try discriminate Hnormalize.
    apply String.eqb_eq in Hliteral. inversion Hnormalize; subst. reflexivity.
  - destruct selected; try discriminate Hnormalize.
    cbn in Hnormalize.
    destruct (String.eqb literal "false") eqn:Hliteral;
      try discriminate Hnormalize.
    apply String.eqb_eq in Hliteral. inversion Hnormalize; subst. reflexivity.
  - destruct selected; try discriminate Hnormalize.
    cbn in Hnormalize.
    destruct (String.eqb literal "unit") eqn:Hliteral;
      try discriminate Hnormalize.
    apply String.eqb_eq in Hliteral. inversion Hnormalize; subst. reflexivity.
  - cbn [phase1_surface_primary_expression_recursive_grouping_branch]
      in Hnormalize.
    destruct (phase1_surface_grouping_lexical_payload
      "char_literal" "CHAR_LITERAL" selected) as [value |] eqn:Hvalue;
      try discriminate Hnormalize.
    inversion Hnormalize; subst expression. cbn.
    rewrite (phase1_surface_grouping_lexical_payload_round_trip _ _ _ _ Hvalue).
    reflexivity.
  - cbn [phase1_surface_primary_expression_recursive_grouping_branch]
      in Hnormalize.
    destruct (phase1_surface_grouping_lexical_payload
      "runtime_string_literal" "STRING_LITERAL" selected)
      as [value |] eqn:Hvalue; try discriminate Hnormalize.
    inversion Hnormalize; subst expression. cbn.
    rewrite (phase1_surface_grouping_lexical_payload_round_trip _ _ _ _ Hvalue).
    reflexivity.
  - cbn [phase1_surface_primary_expression_recursive_grouping_branch]
      in Hnormalize.
    destruct (phase1_surface_grouping_lexical_payload
      "float_literal" "DECIMAL_FLOAT" selected)
      as [value |] eqn:Hvalue; try discriminate Hnormalize.
    inversion Hnormalize; subst expression. cbn.
    rewrite (phase1_surface_grouping_lexical_payload_round_trip _ _ _ _ Hvalue).
    reflexivity.
  - cbn [phase1_surface_primary_expression_recursive_grouping_branch]
      in Hnormalize.
    destruct (phase1_surface_grouping_lexical_payload
      "integer_literal" "DECIMAL_INTEGER" selected)
      as [value |] eqn:Hvalue; try discriminate Hnormalize.
    inversion Hnormalize; subst expression. cbn.
    rewrite (phase1_surface_grouping_lexical_payload_round_trip _ _ _ _ Hvalue).
    reflexivity.
  - discriminate Hnormalize.
Qed.

Theorem phase1_surface_primary_expression_recursive_grouping_from_tree_round_trip :
  forall tree expression,
    phase1_surface_primary_expression_recursive_grouping_from_tree tree =
      Some expression ->
    phase1_surface_primary_expression_recursive_grouping_spine_tree expression =
      phase1_surface_recursive_grouping_tree tree.
Proof.
  intros tree expression Hnormalize.
  destruct tree as
    [literal |class lexeme |name body |items |index body
    | |body |items |inner |inner |first second rest |body |body];
    try discriminate Hnormalize.
  destruct body as
    [literal |class lexeme |inner_name inner_body |items |index selected
    | |inner_body |items |inner |inner |first second rest |inner_body |inner_body];
    try discriminate Hnormalize.
  unfold phase1_surface_primary_expression_recursive_grouping_from_tree
    in Hnormalize.
  destruct (String.eqb name "primary_expression") eqn:Hname;
    try discriminate Hnormalize.
  apply String.eqb_eq in Hname. subst name.
  eapply phase1_surface_primary_expression_recursive_grouping_branch_round_trip.
  exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_primary_expression_recursive_grouping_tree_round_trip :
  forall tree expression,
    phase1_surface_normalize_primary_expression_recursive_grouping_tree tree =
      Some expression ->
    phase1_surface_primary_expression_recursive_grouping_spine_tree expression =
      tree.
Proof.
  intros tree expression Hnormalize.
  unfold phase1_surface_normalize_primary_expression_recursive_grouping_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_recursive_grouping tree)
    as [normalized |] eqn:Hnormalized; try discriminate Hnormalize.
  rewrite
    (phase1_surface_primary_expression_recursive_grouping_from_tree_round_trip
      _ _ Hnormalize).
  eapply phase1_surface_normalize_recursive_grouping_round_trip.
  exact Hnormalized.
Qed.

Theorem phase1_surface_refine_primary_expression_recursive_grouping_round_trip :
  forall previous expression,
    phase1_surface_refine_primary_expression_recursive_grouping previous =
      Some expression ->
    phase1_surface_primary_expression_recursive_grouping_spine_tree expression =
      phase1_surface_primary_expression_integer_spine_tree previous.
Proof.
  intros previous expression Hnormalize.
  eapply phase1_surface_normalize_primary_expression_recursive_grouping_tree_round_trip.
  exact Hnormalize.
Qed.
