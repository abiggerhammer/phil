From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStaticReferenceSpine
  GrammarAstSourceHeaderTotality
  GrammarAstGenericRequirementsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the static-reference spine introduced by #980. *)

Lemma phase1_surface_static_reference_lookup_for_totality :
  lookupRule "static_reference" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "qualified_name";
          EOptional (ENonterminal "static_arguments")
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_named_type_lookup_for_totality :
  lookupRule "named_type" phase1_surface_rules =
    Some (ENonterminal "static_reference").
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_optional_static_arguments_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "static_arguments"))
      input rest tree ->
    exists arguments,
      phase1_surface_normalize_optional_static_arguments tree = Some arguments /\
      phase1_surface_optional_static_arguments_tree arguments = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "static_arguments")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_static_arguments tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_static_arguments_round_trip.
      exact Hnormalize.
  - pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "static_arguments" (descend path AtOptionalBody)
        input rest body Hbody) as Hvalidate.
    assert (Hnormalize :
      phase1_surface_normalize_optional_static_arguments tree =
        Some (Some body)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_static_arguments,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hvalidate.
      reflexivity.
    }
    exists (Some body).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_static_arguments_round_trip.
      exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_static_reference_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "static_reference")
      input rest tree ->
    exists reference,
      phase1_surface_normalize_static_reference_spine tree = Some reference /\
      phase1_surface_static_reference_spine_tree reference = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "static_reference"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_static_reference_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "static_reference"))
      [ ENonterminal "qualified_name";
        EOptional (ENonterminal "static_arguments")
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hname : Derives phase1_surface_rules _
      (ENonterminal "qualified_name") _ _ ?name_tree,
    Harguments : Derives phase1_surface_rules _
      (EOptional (ENonterminal "static_arguments"))
      _ _ ?arguments_tree |- _ =>
      destruct
        (phase1_surface_normalize_qualified_name_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize];
      destruct
        (phase1_surface_normalize_optional_static_arguments_total_from_derivation
          _ _ _ arguments_tree Harguments)
        as [arguments [Harguments_normalize Harguments_round_trip]];
      let reference := constr:(
        {| phase1_static_reference_spine_name := name;
           phase1_static_reference_spine_arguments := arguments |}) in
      assert (Hnormalize :
        phase1_surface_normalize_static_reference_spine tree = Some reference);
      [ rewrite Htree, Hsubtree;
        unfold phase1_surface_normalize_static_reference_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact2;
        cbn;
        rewrite String.eqb_refl;
        rewrite Hname_normalize;
        rewrite Harguments_normalize;
        reflexivity
      | exists reference;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_static_reference_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_named_type_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "named_type")
      input rest tree ->
    exists reference,
      phase1_surface_normalize_named_type_spine tree = Some reference /\
      phase1_surface_named_type_spine_tree reference = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "named_type"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_named_type_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (phase1_surface_normalize_static_reference_spine_total_from_derivation
      (descend path (AtNonterminal "named_type"))
      input rest subtree Hbody)
    as [reference [Hreference Hreference_round_trip]].
  assert (Hnormalize :
    phase1_surface_normalize_named_type_spine tree = Some reference).
  {
    rewrite Htree.
    unfold phase1_surface_normalize_named_type_spine,
      phase1_surface_expect_nonterminal.
    cbn.
    rewrite String.eqb_refl.
    exact Hreference.
  }
  exists reference.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_named_type_spine_round_trip.
    exact Hnormalize.
Qed.
