From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixStaticTermArgumentsSpine
  GrammarAstTermArgumentsTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the named-postfix static term-arguments refinement introduced
  by #1392.

  The carrier advances only the static-leading branch's optional
  term_arguments subtree.  This file proves that normalization is total for
  every derivable present named-postfix tail body while retaining repeated
  projections and the whole term-leading branch as exact certified trees for
  successor refinements.
*)

Lemma
  phase1_surface_normalize_named_postfix_optional_term_arguments_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "term_arguments"))
      input rest tree ->
    exists arguments,
      phase1_surface_normalize_named_postfix_optional_term_arguments tree =
        Some arguments /\
      phase1_surface_named_postfix_optional_term_arguments_tree arguments = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "term_arguments")
      input rest tree Hderive)
    as [[_ Hnone] | [arguments_tree [Hsome Harguments]]].
  - assert (Hnormalize :
      phase1_surface_normalize_named_postfix_optional_term_arguments tree =
        Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_named_postfix_optional_term_arguments_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_term_arguments_spine_total_from_derivation
        _ _ _ arguments_tree Harguments)
      as [arguments [Harguments_normalize Harguments_round_trip]].
    assert (Hnormalize :
      phase1_surface_normalize_named_postfix_optional_term_arguments tree =
        Some (Some arguments)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_named_postfix_optional_term_arguments,
        phase1_surface_expect_optional.
      cbn.
      rewrite Harguments_normalize.
      reflexivity.
    }
    exists (Some arguments).
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_named_postfix_optional_term_arguments_round_trip.
      exact Hnormalize.
Qed.

Theorem
  phase1_surface_normalize_named_postfix_static_term_arguments_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_named_postfix_tail_body_expression_for_totality
      input rest tree ->
    exists refined,
      phase1_surface_normalize_named_postfix_static_term_arguments_tree tree =
        Some refined /\
      phase1_surface_named_postfix_static_term_arguments_spine_tree refined =
        tree.
Proof.
  intros path input rest tree Hderive.
  change
    (Derives phase1_surface_rules path
      (EAlternative phase1_surface_named_postfix_tail_choice_items_for_totality)
      input rest tree) in Hderive.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules path
      phase1_surface_named_postfix_tail_choice_items_for_totality
      input rest tree Hderive)
    as [index [item [selected [Hnth [Htree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules path
        [ ENonterminal "static_arguments";
          EOptional (ENonterminal "term_arguments");
          ERepetition
            phase1_surface_named_postfix_projection_expression_for_totality
        ]
        input rest selected Hselected)
      as [trees [Hselected_tree Hitems]].
    repeat match goal with
    | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
        inversion Hseq; subst; clear Hseq
    end.
    match goal with
    | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
        inversion Hnil; subst; clear Hnil
    end.
    match goal with
    | Hstatic : Derives phase1_surface_rules _
        (ENonterminal "static_arguments") _ _ ?static_arguments_tree |- _ =>
        destruct
          (phase1_surface_normalize_static_arguments_spine_total_from_derivation
            _ _ _ static_arguments_tree Hstatic)
          as [static_arguments
              [Hstatic_normalize Hstatic_round_trip]];
        match goal with
        | Hoptional : Derives phase1_surface_rules _
            (EOptional (ENonterminal "term_arguments"))
            _ _ ?term_arguments_tree,
          Hprojections : Derives phase1_surface_rules _
            (ERepetition
              phase1_surface_named_postfix_projection_expression_for_totality)
            _ _ ?projections_tree |- _ =>
            destruct
              (phase1_surface_normalize_named_postfix_optional_term_arguments_total_from_derivation
                _ _ _ term_arguments_tree Hoptional)
              as [term_arguments
                  [Hterm_arguments_normalize Hterm_arguments_round_trip]];
            let refined := constr:(
              Phase1NamedPostfixStaticTermArgumentsRefined
                static_arguments term_arguments projections_tree) in
            assert (Hnormalize :
              phase1_surface_normalize_named_postfix_static_term_arguments_tree
                tree = Some refined);
            [ rewrite Htree, Hselected_tree;
              unfold
                phase1_surface_normalize_named_postfix_static_term_arguments_tree,
                phase1_surface_normalize_named_postfix_static_arguments_tree,
                phase1_surface_normalize_named_postfix_tail_choice_spine,
                phase1_surface_expect_alternative,
                phase1_surface_normalize_named_postfix_static_arguments_spine,
                phase1_surface_expect_sequence,
                phase1_surface_exact3,
                phase1_surface_normalize_named_postfix_static_term_arguments_spine;
              cbn;
              rewrite Hstatic_normalize, Hterm_arguments_normalize;
              reflexivity
            | exists refined;
              split;
              [ exact Hnormalize
              | eapply
                  phase1_surface_normalize_named_postfix_static_term_arguments_tree_round_trip;
                exact Hnormalize ] ]
        end
    end.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      let refined := constr:(
        Phase1NamedPostfixTermRetainedAfterStaticTermArguments selected) in
      assert (Hnormalize :
        phase1_surface_normalize_named_postfix_static_term_arguments_tree tree =
          Some refined).
      {
        rewrite Htree.
        unfold
          phase1_surface_normalize_named_postfix_static_term_arguments_tree,
          phase1_surface_normalize_named_postfix_static_arguments_tree,
          phase1_surface_normalize_named_postfix_tail_choice_spine,
          phase1_surface_expect_alternative,
          phase1_surface_normalize_named_postfix_static_arguments_spine,
          phase1_surface_normalize_named_postfix_static_term_arguments_spine.
        cbn.
        reflexivity.
      }
      exists refined.
      split.
      * exact Hnormalize.
      * eapply
          phase1_surface_normalize_named_postfix_static_term_arguments_tree_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
