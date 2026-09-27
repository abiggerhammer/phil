From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTupleExpressionSpine
  GrammarAstParenthesizedExpressionSpineTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the tuple-expression spine opened by #1432.

    tuple_expression =
      "(", expression, ",", expression, { ",", expression }, ")" ;

  Every derivable tuple_expression tree is accepted by the structural
  normalizer and reconstructed exactly.  Recursive refinement of the retained
  expression payloads is deliberately left to later expression-layer slices.
*)

Lemma phase1_surface_tuple_expression_lookup_for_totality :
  lookupRule "tuple_expression" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "(";
          ENonterminal "expression";
          ELiteral ",";
          ENonterminal "expression";
          ERepetition
            (ESequence [ELiteral ","; ENonterminal "expression"]);
          ELiteral ")"
        ]).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_normalize_tuple_expression_suffix_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral ","; ENonterminal "expression"])
      input rest tree ->
    exists expression_tree,
      phase1_surface_normalize_tuple_expression_suffix tree =
        Some expression_tree /\
      phase1_surface_tuple_expression_suffix_tree expression_tree = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ELiteral ","; ENonterminal "expression"]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hcomma : Derives phase1_surface_rules _ (ELiteral ",") _ _ ?comma_tree,
    Hexpression : Derives phase1_surface_rules _
      (ENonterminal "expression") _ _ ?expression_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "," _ _ comma_tree Hcomma)
        as [comma_tail [_ [_ Hcomma_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "expression" _ _ _ expression_tree Hexpression)
        as Hexpression_validate;
      assert (Hnormalize :
        phase1_surface_normalize_tuple_expression_suffix tree =
          Some expression_tree);
      [ rewrite Htree, Hcomma_tree;
        unfold phase1_surface_normalize_tuple_expression_suffix,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_literal;
        cbn;
        rewrite Hexpression_validate;
        reflexivity
      | exists expression_tree;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_tuple_expression_suffix_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_tuple_expression_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ESequence [ELiteral ","; ENonterminal "expression"] ->
    exists expressions,
      phase1_surface_normalize_tuple_expression_suffixes trees =
        Some expressions.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists []. reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_tuple_expression_suffix_total_from_derivation
        (descend path AtRepetitionBody) input middle tree Hitem)
      as [expression_tree [Hexpression _]].
    destruct (IHrest eq_refl) as [expressions Hexpressions].
    exists (expression_tree :: expressions).
    cbn.
    rewrite Hexpression, Hexpressions.
    reflexivity.
Qed.

Theorem phase1_surface_normalize_tuple_expression_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "tuple_expression")
      input rest tree ->
    exists tuple_expression,
      phase1_surface_normalize_tuple_expression_spine tree =
        Some tuple_expression /\
      phase1_surface_tuple_expression_spine_tree tuple_expression = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "tuple_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_tuple_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "tuple_expression"))
      [ ELiteral "(";
        ENonterminal "expression";
        ELiteral ",";
        ENonterminal "expression";
        ERepetition
          (ESequence [ELiteral ","; ENonterminal "expression"]);
        ELiteral ")"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hopen : Derives phase1_surface_rules _ (ELiteral "(") _ _ ?open_tree,
    Hfirst : Derives phase1_surface_rules _
      (ENonterminal "expression") _ _ ?first_tree,
    Hcomma : Derives phase1_surface_rules _ (ELiteral ",") _ _ ?comma_tree,
    Hsecond : Derives phase1_surface_rules _
      (ENonterminal "expression") _ _ ?second_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition (ESequence [ELiteral ","; ENonterminal "expression"]))
      _ _ ?rest_tree,
    Hclose : Derives phase1_surface_rules _ (ELiteral ")") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "(" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "expression" _ _ _ first_tree Hfirst)
        as Hfirst_validate;
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "," _ _ comma_tree Hcomma)
        as [comma_tail [_ [_ Hcomma_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "expression" _ _ _ second_tree Hsecond)
        as Hsecond_validate;
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ (ESequence [ELiteral ","; ENonterminal "expression"])
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_body]];
      destruct
        (phase1_surface_normalize_tuple_expression_suffixes_total_from_repetition
          _ (ESequence [ELiteral ","; ENonterminal "expression"])
          _ _ rest_trees Hrest_body eq_refl)
        as [rest_expressions Hrest_normalize];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ")" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      let tuple_expression := constr:(
        {| phase1_tuple_expression_spine_first := first_tree;
           phase1_tuple_expression_spine_second := second_tree;
           phase1_tuple_expression_spine_rest := rest_expressions |}) in
      assert (Hnormalize :
        phase1_surface_normalize_tuple_expression_spine tree =
          Some tuple_expression);
      [ rewrite Htree, Hsubtree, Hopen_tree, Hcomma_tree,
          Hrest_tree, Hclose_tree;
        unfold phase1_surface_normalize_tuple_expression_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact6,
          phase1_surface_expect_literal,
          phase1_surface_expect_repetition;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Hfirst_validate, Hsecond_validate, Hrest_normalize;
        reflexivity
      | exists tuple_expression;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_tuple_expression_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
