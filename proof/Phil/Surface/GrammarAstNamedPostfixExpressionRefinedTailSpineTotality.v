From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixExpressionRefinedTailSpine
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the refined-tail lift introduced by #1412.

  The qualified-name prefix and both present-tail alternatives are now
  structurally refined.  This file proves that the refined-tail
  named_postfix_expression normalizer succeeds for every derivable
  named_postfix_expression tree and reconstructs that exact tree.
*)

Lemma
  phase1_surface_normalize_named_postfix_expression_refined_tail_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_named_postfix_tail_expression_for_totality
      input rest tree ->
    exists raw_tail refined_tail,
      phase1_surface_expect_optional tree = Some raw_tail /\
      phase1_surface_normalize_named_postfix_expression_refined_tail raw_tail =
        Some refined_tail.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_named_postfix_tail_expression_for_totality in Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      phase1_surface_named_postfix_tail_body_expression_for_totality
      input rest tree Hderive)
    as [[_ Hnone] | [body_tree [Hsome Hbody]]].
  - exists None, None.
    split.
    + rewrite Hnone.
      reflexivity.
    + reflexivity.
  - destruct
      (phase1_surface_normalize_named_postfix_term_projection_tree_total_from_derivation
        _ _ _ body_tree Hbody)
      as [refined [Hrefine Hround_trip]].
    exists (Some body_tree), (Some refined).
    split.
    + rewrite Hsome.
      reflexivity.
    + cbn.
      rewrite Hrefine.
      reflexivity.
Qed.

Theorem
  phase1_surface_normalize_named_postfix_expression_refined_tail_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "named_postfix_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_named_postfix_expression_refined_tail_tree tree =
        Some refined /\
      phase1_surface_named_postfix_expression_refined_tail_spine_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "named_postfix_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_named_postfix_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  unfold phase1_surface_named_postfix_expression_for_totality in Hbody.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "named_postfix_expression"))
      [ ENonterminal "qualified_name";
        phase1_surface_named_postfix_tail_expression_for_totality
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
  | Hname : Derives phase1_surface_rules _
      (ENonterminal "qualified_name") _ _ ?name_tree,
    Htail : Derives phase1_surface_rules _
      phase1_surface_named_postfix_tail_expression_for_totality
      _ _ ?tail_tree |- _ =>
      destruct
        (phase1_surface_normalize_qualified_name_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize];
      destruct
        (phase1_surface_normalize_named_postfix_expression_refined_tail_total_from_derivation
          _ _ _ tail_tree Htail)
        as [raw_tail [refined_tail [Htail_expect Htail_refine]]];
      let raw_expression := constr:(
        {| phase1_named_postfix_expression_spine_name := name;
           phase1_named_postfix_expression_spine_tail := raw_tail |}) in
      let refined_expression := constr:(
        {| phase1_named_postfix_expression_refined_tail_name := name;
           phase1_named_postfix_expression_refined_tail := refined_tail |}) in
      assert (Hraw_normalize :
        phase1_surface_normalize_named_postfix_expression_spine tree =
          Some raw_expression);
      [ rewrite Htree, Hsubtree;
        unfold phase1_surface_normalize_named_postfix_expression_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact2;
        cbn;
        rewrite String.eqb_refl;
        rewrite Hname_normalize;
        rewrite Htail_expect;
        reflexivity
      | assert (Hrefined_normalize :
          phase1_surface_normalize_named_postfix_expression_refined_tail_tree
            tree = Some refined_expression);
        [ unfold
            phase1_surface_normalize_named_postfix_expression_refined_tail_tree;
          rewrite Hraw_normalize;
          unfold
            phase1_surface_normalize_named_postfix_expression_refined_tail_spine;
          cbn;
          rewrite Htail_refine;
          reflexivity
        | exists refined_expression;
          split;
          [ exact Hrefined_normalize
          | eapply
              phase1_surface_normalize_named_postfix_expression_refined_tail_tree_round_trip;
            exact Hrefined_normalize ] ] ]
  end.
Qed.
