From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstExpressionBaseChoiceSpine
  GrammarAstExpressionOuterTotality
  GrammarAstBaseExpressionChoiceTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the expression-shell base-choice lift from #1311. *)

Lemma
  phase1_surface_normalize_expression_base_choice_spine_total_from_spine_derivation :
  forall expression path input rest,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest
      (phase1_surface_expression_outer_spine_tree expression) ->
    exists refined,
      phase1_surface_normalize_expression_base_choice_spine expression =
        Some refined.
Proof.
  intros [base fallback] path input rest Hderive.
  unfold phase1_surface_expression_outer_spine_tree in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "expression"
      input rest
      (PTNonterminal "expression"
        (PTSequence
          [ base;
            phase1_surface_optional_expression_fallback_tree fallback
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
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
      input rest
      (PTSequence
        [ base;
          phase1_surface_optional_expression_fallback_tree fallback
        ])
      Hbody)
    as [trees [Hsequence_tree Hitems]].
  inversion Hsequence_tree; subst trees.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hbase : Derives phase1_surface_rules _
      (ENonterminal "base_expression") _ _ base |- _ =>
      destruct
        (phase1_surface_normalize_base_expression_choice_spine_total_from_derivation
          _ _ _ _ Hbase)
        as [refined_base [Hrefined_base Hrefined_round_trip]];
      exists
        {| phase1_expression_base_choice_spine_base := refined_base;
           phase1_expression_base_choice_spine_fallback := fallback |};
      cbn;
      rewrite Hrefined_base;
      reflexivity
  end.
Qed.

Theorem
  phase1_surface_normalize_expression_base_choice_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_expression_base_choice_tree tree =
        Some refined /\
      phase1_surface_expression_base_choice_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_expression_outer_spine_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_expression_base_choice_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_expression_base_choice_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_expression_base_choice_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_expression_base_choice_tree_round_trip.
    exact Hnormalize.
Qed.
