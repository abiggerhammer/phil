From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstParenthesizedExpressionSpine
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the parenthesized-expression spine opened by #1429.

  The structural normalizer already validates the exact grouping shell

    parenthesized_expression = "(", expression, ")" ;

  and retains the nested expression ParseTree. This focused companion proves
  that every derivable parenthesized_expression tree is accepted by that
  normalizer and reconstructed exactly. It deliberately leaves refinement of
  the retained expression payload to later expression-layer slices.
*)

Lemma phase1_surface_parenthesized_expression_lookup_for_totality :
  lookupRule "parenthesized_expression" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "(";
          ENonterminal "expression";
          ELiteral ")"
        ]).
Proof. vm_compute. reflexivity. Qed.

Theorem
  phase1_surface_normalize_parenthesized_expression_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "parenthesized_expression")
      input rest tree ->
    exists grouped,
      phase1_surface_normalize_parenthesized_expression_spine tree =
        Some grouped /\
      phase1_surface_parenthesized_expression_spine_tree grouped = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "parenthesized_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_parenthesized_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "parenthesized_expression"))
      [ ELiteral "(";
        ENonterminal "expression";
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
    Hexpression : Derives phase1_surface_rules _
      (ENonterminal "expression") _ _ ?expression_tree,
    Hclose : Derives phase1_surface_rules _ (ELiteral ")") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "(" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "expression" _ _ _ expression_tree Hexpression)
        as Hexpression_validate;
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ")" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      let grouped := constr:(
        {| phase1_parenthesized_expression_spine_expression :=
             expression_tree |}) in
      assert (Hnormalize :
        phase1_surface_normalize_parenthesized_expression_spine tree =
          Some grouped);
      [ rewrite Htree, Hsubtree, Hopen_tree, Hclose_tree;
        unfold phase1_surface_normalize_parenthesized_expression_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact3,
          phase1_surface_expect_literal;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Hexpression_validate;
        reflexivity
      | exists grouped;
        split;
        [ exact Hnormalize
        | eapply
            phase1_surface_normalize_parenthesized_expression_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
