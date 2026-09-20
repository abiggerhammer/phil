From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectExpressionSpine
  GrammarAstGenericRequirementsTotality
  GrammarAstStaticReferenceTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the effect-expression refinement from #1234. *)

Lemma phase1_surface_effect_expression_lookup_for_totality :
  lookupRule "effect_expression" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "static_reference";
          EOptional (ENonterminal "term_arguments")
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_optional_term_arguments_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "term_arguments"))
      input rest tree ->
    exists arguments,
      phase1_surface_normalize_optional_term_arguments tree = Some arguments /\
      phase1_surface_optional_term_arguments_tree arguments = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "term_arguments")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_term_arguments tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_term_arguments_round_trip.
      exact Hnormalize.
  - pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "term_arguments" (descend path AtOptionalBody)
        input rest body Hbody) as Hvalidate.
    assert (Hnormalize :
      phase1_surface_normalize_optional_term_arguments tree =
        Some (Some body)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_term_arguments,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hvalidate.
      reflexivity.
    }
    exists (Some body).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_term_arguments_round_trip.
      exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_effect_expression_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "effect_expression")
      input rest tree ->
    exists effect,
      phase1_surface_normalize_effect_expression_spine tree = Some effect /\
      phase1_surface_effect_expression_spine_tree effect = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_effect_expression_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "effect_expression"))
      [ ENonterminal "static_reference";
        EOptional (ENonterminal "term_arguments")
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  inversion Hsubtree; subst trees.
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hreference : Derives phase1_surface_rules _
      (ENonterminal "static_reference") _ _ ?reference_tree,
    Harguments : Derives phase1_surface_rules _
      (EOptional (ENonterminal "term_arguments")) _ _ ?arguments_tree |- _ =>
      destruct
        (phase1_surface_normalize_static_reference_spine_total_from_derivation
          _ _ _ reference_tree Hreference)
        as [reference [Hreference_normalize Hreference_round_trip]];
      destruct
        (phase1_surface_normalize_optional_term_arguments_total_from_derivation
          _ _ _ arguments_tree Harguments)
        as [arguments [Harguments_normalize Harguments_round_trip]];
      let effect := constr:(
        {| phase1_effect_expression_spine_reference := reference;
           phase1_effect_expression_spine_arguments := arguments |}) in
      assert (Hnormalize :
        phase1_surface_normalize_effect_expression_spine tree = Some effect);
      [ rewrite Htree;
        unfold phase1_surface_normalize_effect_expression_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact2;
        cbn;
        rewrite String.eqb_refl;
        rewrite Hreference_normalize, Harguments_normalize;
        reflexivity
      | exists effect;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_effect_expression_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
