From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedFuelSupport
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceTotality
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Complete the derivation-driven totality lift for refined shift expressions
  through effect_expression.

  A present optional term_arguments payload receives the finite-fuel witness
  already proved for the completed term_arguments carrier; an absent payload
  succeeds immediately. The enclosing effect-expression spine and arbitrary
  derivable ParseTree then preserve exact reconstruction.

  Structural Rocq surface-correspondence only. This does not change Grammar-v1
  or evaluation semantics, touch Haskell/runtime code, or claim broader
  production-parser soundness/completeness. It continues
  PHIL-SURFACE-GRAMMAR-CORR-001.
*)

Lemma
  phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel_total_from_spine_derivation :
  forall arguments path input rest,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "term_arguments"))
      input rest
      (phase1_surface_optional_term_arguments_expression_fallback_base_choice_tree
        arguments) ->
    exists fuel refined,
      phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel
        fuel arguments = Some refined.
Proof.
  intros [arguments_value |] path input rest Hderive.
  - cbn in Hderive |- *.
    inversion Hderive; subst.
    match goal with
    | Hbody : Derives phase1_surface_rules _
        (ENonterminal "term_arguments") _ _
        (phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
          arguments_value) |- _ =>
        destruct
          (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
            arguments_value _ _ _ Hbody)
          as [fuel [refined Hrefined]];
        exists fuel, (Some refined);
        cbn;
        rewrite Hrefined;
        reflexivity
    end.
  - exists 0, None.
    reflexivity.
Qed.

Lemma
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation :
  forall effect path input rest,
    Derives phase1_surface_rules path (ENonterminal "effect_expression")
      input rest
      (phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
        effect) ->
    exists fuel refined,
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel
        fuel effect = Some refined.
Proof.
  intros [reference arguments] path input rest Hderive.
  unfold
    phase1_surface_effect_expression_expression_fallback_base_choice_spine_tree
    in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_expression"
      input rest
      (PTNonterminal "effect_expression"
        (PTSequence
          [ phase1_surface_static_reference_spine_tree reference;
            phase1_surface_optional_term_arguments_expression_fallback_base_choice_tree
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
          phase1_surface_optional_term_arguments_expression_fallback_base_choice_tree
            arguments
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
      (phase1_surface_optional_term_arguments_expression_fallback_base_choice_tree
        arguments) |- _ =>
      destruct
        (phase1_surface_normalize_optional_term_arguments_expression_fallback_base_choice_shift_refined_fuel_total_from_spine_derivation
          arguments _ _ _ Harguments)
        as [fuel [refined_arguments Hrefined_arguments]];
      exists fuel,
        {| phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference :=
             reference;
           phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments :=
             refined_arguments |};
      cbn;
      rewrite Hrefined_arguments;
      reflexivity
  end.
Qed.

Theorem
  phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_expression")
      input rest tree ->
    exists fuel refined,
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel
        fuel tree = Some refined /\
      phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_spine_fuel_total_from_spine_derivation
      base path input rest Hcanonical)
    as [fuel [refined Hrefined]].
  assert (Hnormalize :
    phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel
      fuel tree = Some refined).
  {
    unfold
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel.
    rewrite Hbase.
    exact Hrefined.
  }
  exists fuel, refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_effect_expression_expression_fallback_base_choice_shift_refined_tree_fuel_round_trip.
    exact Hnormalize.
Qed.
