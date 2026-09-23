From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceSpine
  GrammarAstEffectExpressionExpressionOuterTotality
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the fallback/base-choice lift through effect_expression from
  #1324.

  The carrier introduced there keeps the already-refined static reference and
  advances an optional term_arguments value from the expression-outer carrier
  to the fallback/base-choice carrier. This file proves that refinement is
  total for derivable effect_expression trees.
*)

Lemma
  phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_total_from_spine_derivation :
  forall arguments path input rest,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "term_arguments"))
      input rest
      (phase1_surface_optional_term_arguments_expression_outer_tree arguments) ->
    exists refined,
      phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice
        arguments = Some refined.
Proof.
  intros [arguments_value |] path input rest Hderive.
  - cbn in Hderive |- *.
    inversion Hderive; subst.
    match goal with
    | Hbody : Derives phase1_surface_rules _
        (ENonterminal "term_arguments") _ _
        (phase1_surface_term_arguments_expression_outer_spine_tree
          arguments_value) |- _ =>
        destruct
          (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine_total_from_spine_derivation
            arguments_value _ _ _ Hbody)
          as [refined Hrefined];
        exists (Some refined);
        cbn;
        rewrite Hrefined;
        reflexivity
    end.
  - cbn.
    exists None.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_spine_total_from_spine_derivation :
  forall effect path input rest,
    Derives phase1_surface_rules path (ENonterminal "effect_expression")
      input rest
      (phase1_surface_effect_expression_expression_outer_spine_tree effect) ->
    exists refined,
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_spine
        effect = Some refined.
Proof.
  intros [reference arguments] path input rest Hderive.
  unfold phase1_surface_effect_expression_expression_outer_spine_tree in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_expression"
      input rest
      (PTNonterminal "effect_expression"
        (PTSequence
          [ phase1_surface_static_reference_spine_tree reference;
            phase1_surface_optional_term_arguments_expression_outer_tree
              arguments
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "effect_expression"))
      [ ENonterminal "static_reference";
        EOptional (ENonterminal "term_arguments")
      ]
      input rest
      (PTSequence
        [ phase1_surface_static_reference_spine_tree reference;
          phase1_surface_optional_term_arguments_expression_outer_tree arguments
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
  | Harguments : Derives phase1_surface_rules _
      (EOptional (ENonterminal "term_arguments"))
      _ _
      (phase1_surface_optional_term_arguments_expression_outer_tree arguments)
      |- _ =>
      destruct
        (phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_total_from_spine_derivation
          arguments _ _ _ Harguments)
        as [refined_arguments Hrefined_arguments];
      exists
        {| phase1_effect_expression_expression_fallback_base_choice_spine_reference :=
             reference;
           phase1_effect_expression_expression_fallback_base_choice_spine_arguments :=
             refined_arguments |};
      cbn;
      rewrite Hrefined_arguments;
      reflexivity
  end.
Qed.

Theorem
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree
        tree = Some refined /\
      phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_effect_expression_expression_outer_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree
      tree = Some refined).
  {
    unfold
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree_round_trip.
    exact Hnormalize.
Qed.
