From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceSpine
  GrammarAstTermArgumentsExpressionOuterTotality
  GrammarAstExpressionFallbackBaseChoiceTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the fallback/base-choice lift through term_arguments from #1320.

  The carrier introduced there refines every already-outer-certified expression
  argument through the command/shift base choice and fail/reject fallback
  choice.  This file proves that refinement is total for derivable
  term_arguments trees.
*)

Lemma
  phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine_total_from_derivation :
  forall expression path input rest,
    Derives phase1_surface_rules path (ENonterminal "expression")
      input rest (phase1_surface_expression_outer_spine_tree expression) ->
    exists refined,
      phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine
        expression = Some refined.
Proof.
  intros expression path input rest Hderive.
  destruct
    (phase1_surface_normalize_expression_base_choice_spine_total_from_spine_derivation
      expression path input rest Hderive)
    as [base Hbase].
  pose proof Hderive as Hcanonical.
  rewrite <-
    (phase1_surface_normalize_expression_base_choice_spine_round_trip
      expression base Hbase)
    in Hcanonical.
  destruct
    (phase1_surface_normalize_expression_fallback_base_choice_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  exists refined.
  unfold
    phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine.
  rewrite Hbase.
  exact Hrefined.
Qed.

Lemma
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_values_total_from_suffix_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ESequence [ELiteral ","; ENonterminal "expression"] ->
    forall arguments,
      trees =
        map phase1_surface_term_argument_expression_outer_suffix_tree arguments ->
      exists refined,
        phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
          arguments = Some refined.
Proof.
  intros path body input rest trees Hderive Hbody_shape.
  subst body.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hitem Hprogress Hrest IHrest];
    intros arguments Htrees.
  - destruct arguments as [|argument arguments]; cbn in Htrees.
    + exists [].
      reflexivity.
    + discriminate Htrees.
  - destruct arguments as [|argument arguments]; cbn in Htrees;
      try discriminate Htrees.
    inversion Htrees; subst tree trees.
    unfold phase1_surface_term_argument_expression_outer_suffix_tree in Hitem.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend path AtRepetitionBody)
        [ ELiteral ",";
          ENonterminal "expression"
        ]
        input middle
        (PTSequence
          [ PTLiteral ",";
            phase1_surface_expression_outer_spine_tree argument
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
    | Hargument : Derives phase1_surface_rules _
        (ENonterminal "expression")
        _ _ (phase1_surface_expression_outer_spine_tree argument) |- _ =>
        destruct
          (phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine_total_from_derivation
            argument _ _ _ Hargument)
          as [refined_argument Hrefined_argument];
        destruct (IHrest arguments eq_refl)
          as [refined_rest Hrefined_rest];
        exists (refined_argument :: refined_rest);
        cbn;
        rewrite Hrefined_argument, Hrefined_rest;
        reflexivity
    end.
Qed.

Lemma
  phase1_surface_normalize_term_argument_expression_fallback_base_choice_values_total_from_entries_derivation :
  forall arguments path input rest,
    Derives phase1_surface_rules path
      (EOptional
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ])
          ]))
      input rest
      (phase1_surface_term_argument_expression_outer_entries_tree arguments) ->
    exists refined,
      phase1_surface_normalize_term_argument_expression_fallback_base_choice_values
        arguments = Some refined.
Proof.
  intros arguments path input rest Hderive.
  destruct arguments as [|first rest_arguments].
  - exists [].
    reflexivity.
  - cbn in Hderive |- *.
    inversion Hderive; subst.
    match goal with
    | Hbody : Derives phase1_surface_rules _
        (ESequence
          [ ENonterminal "expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ])
          ])
        _ _
        (PTSequence
          [ phase1_surface_expression_outer_spine_tree first;
            PTRepetition
              (map
                phase1_surface_term_argument_expression_outer_suffix_tree
                rest_arguments)
          ]) |- _ =>
        destruct
          (derives_sequence_expression_exposes_items
            phase1_surface_rules _
            [ ENonterminal "expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
            ]
            _ _
            (PTSequence
              [ phase1_surface_expression_outer_spine_tree first;
                PTRepetition
                  (map
                    phase1_surface_term_argument_expression_outer_suffix_tree
                    rest_arguments)
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
            (ENonterminal "expression")
            _ _ (phase1_surface_expression_outer_spine_tree first),
          Hrepeat : Derives phase1_surface_rules _
            (ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ]))
            _ _
            (PTRepetition
              (map
                phase1_surface_term_argument_expression_outer_suffix_tree
                rest_arguments)) |- _ =>
            destruct
              (phase1_surface_normalize_expression_fallback_base_choice_from_outer_spine_total_from_derivation
                first _ _ _ Hfirst)
              as [refined_first Hrefined_first];
            destruct
              (phase1_surface_repetition_derivation_exposes
                _
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
                _ _
                (PTRepetition
                  (map
                    phase1_surface_term_argument_expression_outer_suffix_tree
                    rest_arguments))
                Hrepeat)
              as [rest_trees [Hrest_tree Hrest_body]];
            inversion Hrest_tree; subst rest_trees;
            destruct
              (phase1_surface_normalize_term_argument_expression_fallback_base_choice_values_total_from_suffix_repetition
                _
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
                _ _
                (map
                  phase1_surface_term_argument_expression_outer_suffix_tree
                  rest_arguments)
                Hrest_body eq_refl
                rest_arguments eq_refl)
              as [refined_rest Hrefined_rest];
            exists (refined_first :: refined_rest);
            cbn;
            rewrite Hrefined_first, Hrefined_rest;
            reflexivity
        end
    end.
Qed.

Lemma
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine_total_from_spine_derivation :
  forall arguments path input rest,
    Derives phase1_surface_rules path (ENonterminal "term_arguments")
      input rest
      (phase1_surface_term_arguments_expression_outer_spine_tree arguments) ->
    exists refined,
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine
        arguments = Some refined.
Proof.
  intros [arguments] path input rest Hderive.
  unfold phase1_surface_term_arguments_expression_outer_spine_tree in Hderive.
  cbn in Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "term_arguments"
      input rest
      (PTNonterminal "term_arguments"
        (PTSequence
          [ PTLiteral "(";
            phase1_surface_term_argument_expression_outer_entries_tree arguments;
            PTLiteral ")"
          ]))
      Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_term_arguments_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  inversion Htree; subst subtree.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "term_arguments"))
      [ ELiteral "(";
        EOptional
          (ESequence
            [ ENonterminal "expression";
              ERepetition
                (ESequence
                  [ ELiteral ",";
                    ENonterminal "expression"
                  ])
            ]);
        ELiteral ")"
      ]
      input rest
      (PTSequence
        [ PTLiteral "(";
          phase1_surface_term_argument_expression_outer_entries_tree arguments;
          PTLiteral ")"
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
          [ ENonterminal "expression";
            ERepetition
              (ESequence
                [ ELiteral ",";
                  ENonterminal "expression"
                ])
          ]))
      _ _
      (phase1_surface_term_argument_expression_outer_entries_tree arguments) |- _ =>
      destruct
        (phase1_surface_normalize_term_argument_expression_fallback_base_choice_values_total_from_entries_derivation
          arguments _ _ _ Hentries)
        as [refined_arguments Hrefined_arguments];
      exists
        {| phase1_term_arguments_expression_fallback_base_choice_spine_arguments :=
             refined_arguments |};
      cbn;
      rewrite Hrefined_arguments;
      reflexivity
  end.
Qed.

Theorem
  phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "term_arguments")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree
        tree = Some refined /\
      phase1_surface_term_arguments_expression_fallback_base_choice_spine_tree
        refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_term_arguments_expression_outer_tree_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  pose proof Hderive as Hcanonical.
  rewrite <- Hbase_round_trip in Hcanonical.
  destruct
    (phase1_surface_normalize_term_arguments_expression_fallback_base_choice_spine_total_from_spine_derivation
      base path input rest Hcanonical)
    as [refined Hrefined].
  assert (Hnormalize :
    phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree
      tree = Some refined).
  {
    unfold
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply
      phase1_surface_normalize_term_arguments_expression_fallback_base_choice_tree_round_trip.
    exact Hnormalize.
Qed.
