From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstExpressionOuterSpine
  GrammarAstGenericRequirementsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the outer expression refinement from #1272. *)

Lemma phase1_surface_expression_lookup_for_totality :
  lookupRule "expression" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "base_expression";
          EOptional
            (ESequence
              [ ELiteral "or";
                ENonterminal "fallback"
              ])
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma
  phase1_surface_normalize_expression_fallback_tail_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral "or"; ENonterminal "fallback"])
      input rest tree ->
    exists fallback,
      phase1_surface_normalize_expression_fallback_tail tree = Some fallback /\
      phase1_surface_expression_fallback_tail_tree fallback = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "or";
        ENonterminal "fallback"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral "or")
      [ ENonterminal "fallback" ]
      input rest trees Hitems)
    as [after_or [or_tree [tail_trees
      [Htrees [Hor Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "fallback") []
      after_or rest tail_trees Htail)
    as [after_fallback [fallback_tree [nil_trees
      [Htail_trees [Hfallback Hnil]]]]].
  rewrite Htrees, Htail_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "or" _ _ or_tree Hor)
    as [or_tail [_ [_ Hor_tree]]].
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "fallback" _ _ _ fallback_tree Hfallback) as Hfallback_validate.
  assert (Hnormalize :
    phase1_surface_normalize_expression_fallback_tail tree =
      Some fallback_tree).
  {
    rewrite Htree, Hor_tree.
    unfold phase1_surface_normalize_expression_fallback_tail,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hfallback_validate.
    reflexivity.
  }
  exists fallback_tree.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_expression_fallback_tail_round_trip.
    exact Hnormalize.
Qed.

Lemma
  phase1_surface_normalize_optional_expression_fallback_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ELiteral "or";
            ENonterminal "fallback"
          ]))
      input rest tree ->
    exists fallback,
      phase1_surface_normalize_optional_expression_fallback tree =
        Some fallback /\
      phase1_surface_optional_expression_fallback_tree fallback = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ESequence
        [ ELiteral "or";
          ENonterminal "fallback"
        ])
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_expression_fallback tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_optional_expression_fallback_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_expression_fallback_tail_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [fallback [Hfallback Hfallback_round_trip]].
    assert (Hnormalize :
      phase1_surface_normalize_optional_expression_fallback tree =
        Some (Some fallback)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_expression_fallback,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hfallback.
      reflexivity.
    }
    exists (Some fallback).
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_optional_expression_fallback_round_trip.
      exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_expression_outer_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest tree ->
    exists expression,
      phase1_surface_normalize_expression_outer_spine tree = Some expression /\
      phase1_surface_expression_outer_spine_tree expression = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "expression"))
      [ ENonterminal "base_expression";
        EOptional
          (ESequence
            [ ELiteral "or";
              ENonterminal "fallback"
            ])
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "expression")) 0
      (ENonterminal "base_expression")
      [ EOptional
          (ESequence
            [ ELiteral "or";
              ENonterminal "fallback"
            ])
      ]
      input rest trees Hitems)
    as [after_base [base_tree [tail_trees
      [Htrees [Hbase Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "expression")) 1
      (EOptional
        (ESequence
          [ ELiteral "or";
            ENonterminal "fallback"
          ]))
      []
      after_base rest tail_trees Htail)
    as [after_fallback [fallback_tree [nil_trees
      [Htail_trees [Hfallback Hnil]]]]].
  rewrite Htrees, Htail_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "base_expression" _ _ _ base_tree Hbase) as Hbase_validate.
  destruct
    (phase1_surface_normalize_optional_expression_fallback_total_from_derivation
      _ _ _ fallback_tree Hfallback)
    as [fallback [Hfallback_normalize Hfallback_round_trip]].
  pose (expression :=
    {| phase1_expression_outer_spine_base := base_tree;
       phase1_expression_outer_spine_fallback := fallback |}).
  assert (Hnormalize :
    phase1_surface_normalize_expression_outer_spine tree =
      Some expression).
  {
    rewrite Htree, Hsubtree.
    unfold phase1_surface_normalize_expression_outer_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact2.
    cbn.
    rewrite Hbase_validate, Hfallback_normalize.
    reflexivity.
  }
  exists expression.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_expression_outer_spine_round_trip.
    exact Hnormalize.
Qed.
