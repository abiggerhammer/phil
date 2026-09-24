From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstNamedPostfixTailChoiceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Converse for the named-postfix tail-choice refinement introduced by #1384.

  The carrier exposes the static-leading-versus-term-leading alternative while
  retaining the selected branch body as its exact certified ParseTree.  This
  file proves that normalization is total for every derivable present
  named-postfix tail body, leaving static arguments, term arguments, and
  repeated projections as dedicated successor refinement boundaries.
*)

Definition phase1_surface_named_postfix_tail_choice_items_for_totality
  : list EbnfExpression :=
  [ ESequence
      [ ENonterminal "static_arguments";
        EOptional (ENonterminal "term_arguments");
        ERepetition
          phase1_surface_named_postfix_projection_expression_for_totality
      ];
    ESequence
      [ ENonterminal "term_arguments";
        ERepetition
          phase1_surface_named_postfix_projection_expression_for_totality
      ]
  ].

Theorem phase1_surface_normalize_named_postfix_tail_choice_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_named_postfix_tail_body_expression_for_totality
      input rest tree ->
    exists tail,
      phase1_surface_normalize_named_postfix_tail_choice_spine tree = Some tail /\
      phase1_surface_named_postfix_tail_choice_spine_tree tail = tree.
Proof.
  intros path input rest tree Hderive.
  change
    (Derives phase1_surface_rules path
      (EAlternative
        phase1_surface_named_postfix_tail_choice_items_for_totality)
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
    assert (Hnormalize :
      phase1_surface_normalize_named_postfix_tail_choice_spine tree =
        Some (Phase1SurfaceNamedPostfixTailStatic selected)).
    {
      rewrite Htree.
      unfold phase1_surface_normalize_named_postfix_tail_choice_spine,
        phase1_surface_expect_alternative.
      cbn.
      reflexivity.
    }
    exists (Phase1SurfaceNamedPostfixTailStatic selected).
    split.
    + exact Hnormalize.
    + eapply
        phase1_surface_normalize_named_postfix_tail_choice_spine_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      assert (Hnormalize :
        phase1_surface_normalize_named_postfix_tail_choice_spine tree =
          Some (Phase1SurfaceNamedPostfixTailTerm selected)).
      {
        rewrite Htree.
        unfold phase1_surface_normalize_named_postfix_tail_choice_spine,
          phase1_surface_expect_alternative.
        cbn.
        reflexivity.
      }
      exists (Phase1SurfaceNamedPostfixTailTerm selected).
      split.
      * exact Hnormalize.
      * eapply
          phase1_surface_normalize_named_postfix_tail_choice_spine_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
