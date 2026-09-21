From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetExpressionOuterSpine
  GrammarAstEffectSetTermArgumentsTotality
  GrammarAstEffectExpressionExpressionOuterTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the expression-outer lift through effect sets from #1283. *)

Lemma
  phase1_surface_normalize_effect_expression_expression_outer_values_total_from_suffix_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body =
      ESequence [ELiteral ","; ENonterminal "effect_expression"] ->
    forall effects,
      trees =
        map phase1_surface_effect_expression_term_arguments_suffix_tree effects ->
      exists refined,
        phase1_surface_normalize_effect_expression_expression_outer_values
          effects = Some refined.
Proof.
  intros path body input rest trees Hderive Hbody_shape.
  subst body.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros effects Htrees.
  - destruct effects as [|effect effects]; cbn in Htrees.
    + exists [].
      reflexivity.
    + discriminate Htrees.
  - destruct effects as [|effect effects]; cbn in Htrees;
      try discriminate Htrees.
    inversion Htrees; subst tree trees.
    unfold phase1_surface_effect_expression_term_arguments_suffix_tree in Hitem.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtRepetitionBody)
        [ ELiteral ",";
          ENonterminal "effect_expression"
        ]
        input middle
        (PTSequence
          [ PTLiteral ",";
            phase1_surface_effect_expression_term_arguments_spine_tree effect
          ])
        Hitem)
      as [item_trees [Hitem_tree Hitem_items]].
    inversion Hitem_tree; subst item_trees.
    repeat match goal with
    | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
        inversion Hseq; subst; clear Hseq
    end.
    match goal with
    | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
        inversion Hnil; subst; clear Hnil
    end.
    match goal with
    | Heffect : Derives phase1_surface_rules _
        (ENonterminal "effect_expression")
        _ _ (phase1_surface_effect_expression_term_arguments_spine_tree effect)
        |- _ =>
        destruct
          (phase1_surface_normalize_effect_expression_expression_outer_spine_total_from_spine_derivation
            effect _ _ _ Heffect)
          as [refined_effect Hrefined_effect];
        destruct (IHrest effects eq_refl)
          as [refined_rest Hrefined_rest];
        exists (refined_effect :: refined_rest);
        cbn;
        rewrite Hrefined_effect, Hrefined_rest;
        reflexivity
    end.
Qed.

Lemma
  phase1_surface_normalize_effect_expression_expression_outer_values_total_from_entries_derivation :
  forall effects path input rest,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "effect_expression"
                ])
          ]))
      input rest
      (phase1_surface_effect_expression_term_arguments_entries_tree effects) ->
    exists refined,
      phase1_surface_normalize_effect_expression_expression_outer_values effects =
        Some refined.
Proof.
  intros effects path input rest Hderive.
  destruct effects as [|first rest_effects].
  - exists [].
    reflexivity.
  - cbn in Hderive |- *.
    inversion Hderive; subst.
    match goal with
    | Hbody : Derives phase1_surface_rules _
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "effect_expression"
                ])
          ])
        _ _
        (PTSequence
          [ phase1_surface_effect_expression_term_arguments_spine_tree first;
            PTRepetition
              (map
                phase1_surface_effect_expression_term_arguments_suffix_tree
                rest_effects)
          ]) |- _ =>
        destruct
          (derives_sequence_expression_exposes_items
            phase1_surface_rules _
            [ ENonterminal "effect_expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "effect_expression"
                  ])
            ]
            _ _
            (PTSequence
              [ phase1_surface_effect_expression_term_arguments_spine_tree first;
                PTRepetition
                  (map
                    phase1_surface_effect_expression_term_arguments_suffix_tree
                    rest_effects)
              ])
            Hbody)
          as [trees [Htree Hitems]];
        inversion Htree; subst trees;
        repeat match goal with
        | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
            inversion Hseq; subst; clear Hseq
        end;
        match goal with
        | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
            inversion Hnil; subst; clear Hnil
        end;
        match goal with
        | Hfirst : Derives phase1_surface_rules _
            (ENonterminal "effect_expression")
            _ _
            (phase1_surface_effect_expression_term_arguments_spine_tree first),
          Hrepeat : Derives phase1_surface_rules _
            (ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "effect_expression"
                ]))
            _ _
            (PTRepetition
              (map
                phase1_surface_effect_expression_term_arguments_suffix_tree
                rest_effects)) |- _ =>
            destruct
              (phase1_surface_normalize_effect_expression_expression_outer_spine_total_from_spine_derivation
                first _ _ _ Hfirst)
              as [refined_first Hrefined_first];
            destruct
              (phase1_surface_repetition_derivation_exposes
                _
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "effect_expression"
                  ])
                _ _
                (PTRepetition
                  (map
                    phase1_surface_effect_expression_term_arguments_suffix_tree
                    rest_effects))
                Hrepeat)
              as [rest_trees [Hrest_tree Hrest_body]];
            inversion Hrest_tree; subst rest_trees;
            destruct
              (phase1_surface_normalize_effect_expression_expression_outer_values_total_from_suffix_repetition
                _
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "effect_expression"
                  ])
                _ _
                (map
                  phase1_surface_effect_expression_term_arguments_suffix_tree
                  rest_effects)
                Hrest_body eq_refl
                rest_effects eq_refl)
              as [refined_rest Hrefined_rest];
            exists (refined_first :: refined_rest);
            cbn;
            rewrite Hrefined_first, Hrefined_rest;
            reflexivity
        end
    end.
Qed.

Lemma
  phase1_surface_normalize_effect_set_expression_outer_literal_spine_total_from_spine_derivation :
  forall literal path input rest,
    Derives phase1_surface_rules path (ENonterminal "effect_set_literal")
      input rest
      (phase1_surface_effect_set_term_arguments_literal_spine_tree literal) ->
    exists refined,
      phase1_surface_normalize_effect_set_expression_outer_literal_spine literal =
        Some refined.
Proof.
  intros [effects] path input rest Hderive.
  unfold phase1_surface_effect_set_term_arguments_literal_spine_tree in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_set_literal"
      input rest
      (PTNonterminal "effect_set_literal"
        (PTSequence
          [ PTLiteral "{";
            phase1_surface_effect_expression_term_arguments_entries_tree effects;
            PTLiteral "}"
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_set_literal_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal"))
      [ ELiteral "{";
        EOptional
          (ESequence
            [ ENonterminal "effect_expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "effect_expression"
                  ])
            ]);
        ELiteral "}"
      ]
      input rest
      (PTSequence
        [ PTLiteral "{";
          phase1_surface_effect_expression_term_arguments_entries_tree effects;
          PTLiteral "}"
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
  | Hentries : Derives phase1_surface_rules _
      (EOptional
        (ESequence
          [ ENonterminal "effect_expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "effect_expression"
                ])
          ]))
      _ _ (phase1_surface_effect_expression_term_arguments_entries_tree effects)
      |- _ =>
      destruct
        (phase1_surface_normalize_effect_expression_expression_outer_values_total_from_entries_derivation
          effects _ _ _ Hentries)
        as [refined_effects Hrefined_effects];
      exists
        {| phase1_effect_set_expression_outer_literal_spine_effects :=
             refined_effects |};
      cbn;
      rewrite Hrefined_effects;
      reflexivity
  end.
Qed.

Lemma
  phase1_surface_normalize_effect_set_expression_outer_spine_total_from_spine_derivation :
  forall effects path input rest,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest
      (phase1_surface_effect_set_term_arguments_spine_tree effects) ->
    exists refined,
      phase1_surface_normalize_effect_set_expression_outer_spine effects =
        Some refined.
Proof.
  intros effects path input rest Hderive.
  destruct effects as [literal | reference].
  - cbn in Hderive |- *.
    destruct
      (derives_nonterminal_exposes_body
        phase1_surface_rules path "effect_set_expression"
        input rest
        (PTNonterminal "effect_set_expression"
          (PTAlternative 0
            (phase1_surface_effect_set_term_arguments_literal_spine_tree
              literal)))
        Hderive)
      as [body [subtree [Hlookup [Htree Hbody]]]].
    rewrite phase1_surface_effect_set_expression_lookup_for_totality in Hlookup.
    inversion Hlookup; subst body.
    inversion Htree; subst subtree.
    destruct
      (alternative_derivation_names_exact_branch
        phase1_surface_rules
        (descend path (AtNonterminal "effect_set_expression"))
        [ ENonterminal "effect_set_literal";
          ENonterminal "static_reference"
        ]
        input rest
        (PTAlternative 0
          (phase1_surface_effect_set_term_arguments_literal_spine_tree literal))
        Hbody)
      as [index [item [selected [Hnth [Hbranch Hselected]]]]].
    inversion Hbranch; subst index selected.
    cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_effect_set_expression_outer_literal_spine_total_from_spine_derivation
        literal _ _ _ Hselected)
      as [refined_literal Hrefined_literal].
    exists (Phase1EffectSetExpressionOuterLiteral refined_literal).
    rewrite Hrefined_literal.
    reflexivity.
  - exists (Phase1EffectSetExpressionOuterReference reference).
    reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_set_expression_outer_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_set_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_effect_set_expression_outer_tree tree =
        Some refined /\
      phase1_surface_effect_set_expression_outer_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_effect_set_term_arguments_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_effect_set_expression_outer_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_effect_set_expression_outer_tree tree =
      Some refined).
  {
    unfold phase1_surface_normalize_effect_set_expression_outer_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_effect_set_expression_outer_tree_round_trip.
    exact Hnormalize.
Qed.
