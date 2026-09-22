From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementExpressionOuterSpine
  GrammarAstGenericRequirementEffectsTotality
  GrammarAstEffectSetExpressionOuterTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the expression-outer lift into the generic effects requirement. *)

Lemma
  phase1_surface_normalize_generic_requirement_expression_outer_spine_total_from_spine_derivation :
  forall requirement path input rest,
    Derives phase1_surface_rules path
      (ENonterminal "generic_requirement")
      input rest
      (phase1_surface_generic_requirement_effects_spine_tree requirement) ->
    exists refined,
      phase1_surface_normalize_generic_requirement_expression_outer_spine
        requirement = Some refined.
Proof.
  intros requirement path input rest Hderive.
  destruct requirement; cbn in Hderive |- *.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules path "generic_requirement"
        input rest
        (PTNonterminal "generic_requirement"
          (PTAlternative 6
            (PTSequence
              [ PTLiteral "effects";
                name_tree;
                PTLiteral "within";
                phase1_surface_effect_set_term_arguments_spine_tree effects;
                PTLiteral ";"
              ])))
        Hderive)
      as [body [subtree [Hlookup [Htree Hbody]]]].
    rewrite phase1_surface_generic_requirement_lookup_for_totality in Hlookup.
    inversion Hlookup; subst body.
    inversion Htree; subst subtree.
    destruct
      (alternative_derivation_names_exact_branch
        phase1_surface_rules
        (descend path (AtNonterminal "generic_requirement"))
        phase1_surface_generic_requirement_items_for_totality
        input rest
        (PTAlternative 6
          (PTSequence
            [ PTLiteral "effects";
              name_tree;
              PTLiteral "within";
              phase1_surface_effect_set_term_arguments_spine_tree effects;
              PTLiteral ";"
            ]))
        Hbody)
      as [index [item [selected [Hnth [Hbranch Hselected]]]]].
    inversion Hbranch; subst index selected.
    cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        _
        [ ELiteral "effects";
          ENonterminal "identifier";
          ELiteral "within";
          ENonterminal "effect_set_expression";
          ELiteral ";"
        ]
        _ _
        (PTSequence
          [ PTLiteral "effects";
            name_tree;
            PTLiteral "within";
            phase1_surface_effect_set_term_arguments_spine_tree effects;
            PTLiteral ";"
          ])
        Hselected)
      as [trees [Hselected_tree Hitems]].
    inversion Hselected_tree; subst trees.
    repeat match goal with
    | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
        inversion Hseq; subst; clear Hseq
    end.
    match goal with
    | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
        inversion Hnil; subst; clear Hnil
    end.
    match goal with
    | Heffects : Derives phase1_surface_rules _
        (ENonterminal "effect_set_expression")
        _ _ (phase1_surface_effect_set_term_arguments_spine_tree effects)
        |- _ =>
        destruct
          (phase1_surface_normalize_effect_set_expression_outer_spine_total_from_spine_derivation
            effects _ _ _ Heffects)
          as [refined_effects Hrefined_effects];
        exists
          (Phase1GenericEffectsExpressionOuterRequirement
            name_tree refined_effects);
        cbn;
        rewrite Hrefined_effects;
        reflexivity
    end.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
Qed.

Theorem
  phase1_surface_normalize_generic_requirement_expression_outer_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirement")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_generic_requirement_expression_outer_tree tree =
        Some refined /\
      phase1_surface_generic_requirement_expression_outer_spine_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_generic_requirement_effects_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_generic_requirement_expression_outer_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_generic_requirement_expression_outer_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_generic_requirement_expression_outer_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_generic_requirement_expression_outer_tree_round_trip.
    exact Hnormalize.
Qed.
