From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStaticArgumentsSpine
  GrammarAstStaticReferenceTotality
  GrammarAstSourceHeaderTotality
  GrammarAstGenericRequirementsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the static-argument list/category correspondence from #984. *)

Definition phase1_surface_static_argument_items_for_totality
  : list EbnfExpression :=
  [ ENonterminal "nonreference_type_expression";
    ENonterminal "nonreference_session_expression";
    ENonterminal "static_value_expression";
    ENonterminal "effect_set_literal"
  ].

Definition phase1_surface_static_argument_suffix_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral ",";
      ENonterminal "static_argument"
    ].

Definition phase1_surface_static_argument_list_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ENonterminal "static_argument";
      ERepetition phase1_surface_static_argument_suffix_expression_for_totality
    ].

Definition phase1_surface_optional_static_argument_list_expression_for_totality
  : EbnfExpression :=
  EOptional phase1_surface_static_argument_list_expression_for_totality.

Definition phase1_surface_static_arguments_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "[";
      phase1_surface_optional_static_argument_list_expression_for_totality;
      ELiteral "]"
    ].

Lemma phase1_surface_static_argument_lookup_for_totality :
  lookupRule "static_argument" phase1_surface_rules =
    Some (EAlternative phase1_surface_static_argument_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_static_arguments_lookup_for_totality :
  lookupRule "static_arguments" phase1_surface_rules =
    Some phase1_surface_static_arguments_expression_for_totality.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_static_argument_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "static_argument")
      input rest tree ->
    exists argument,
      phase1_surface_normalize_static_argument_spine tree = Some argument /\
      phase1_surface_static_argument_spine_tree argument = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "static_argument"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_static_argument_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "static_argument"))
      phase1_surface_static_argument_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "nonreference_type_expression" _ _ _ selected Hselected)
      as Hvalidate.
    let argument := constr:(
      {| phase1_static_argument_spine_tag := Phase1StaticTypeArgument;
         phase1_static_argument_spine_selected_tree := selected |}) in
    assert (Hnormalize :
      phase1_surface_normalize_static_argument_spine tree = Some argument).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_static_argument_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative,
        phase1_surface_validate_static_argument_selected,
        phase1_surface_static_argument_tag_name.
      cbn.
      rewrite Hvalidate.
      reflexivity.
    }
    exists argument.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_static_argument_spine_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "nonreference_session_expression" _ _ _ selected Hselected)
        as Hvalidate.
      let argument := constr:(
        {| phase1_static_argument_spine_tag := Phase1StaticSessionArgument;
           phase1_static_argument_spine_selected_tree := selected |}) in
      assert (Hnormalize :
        phase1_surface_normalize_static_argument_spine tree = Some argument).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_static_argument_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative,
          phase1_surface_validate_static_argument_selected,
          phase1_surface_static_argument_tag_name.
        cbn.
        rewrite Hvalidate.
        reflexivity.
      }
      exists argument.
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_static_argument_spine_round_trip.
        exact Hnormalize.
    + destruct index as [|index].
      * cbn in Hnth.
        inversion Hnth; subst item.
        pose proof
          (phase1_surface_validate_named_node_total_from_derivation
            "static_value_expression" _ _ _ selected Hselected)
          as Hvalidate.
        let argument := constr:(
          {| phase1_static_argument_spine_tag := Phase1StaticValueArgument;
             phase1_static_argument_spine_selected_tree := selected |}) in
        assert (Hnormalize :
          phase1_surface_normalize_static_argument_spine tree = Some argument).
        {
          rewrite Htree, Hsubtree.
          unfold phase1_surface_normalize_static_argument_spine,
            phase1_surface_expect_nonterminal,
            phase1_surface_expect_alternative,
            phase1_surface_validate_static_argument_selected,
            phase1_surface_static_argument_tag_name.
          cbn.
          rewrite Hvalidate.
          reflexivity.
        }
        exists argument.
        split.
        -- exact Hnormalize.
        -- eapply phase1_surface_normalize_static_argument_spine_round_trip.
           exact Hnormalize.
      * destruct index as [|index].
        -- cbn in Hnth.
           inversion Hnth; subst item.
           pose proof
             (phase1_surface_validate_named_node_total_from_derivation
               "effect_set_literal" _ _ _ selected Hselected)
             as Hvalidate.
           let argument := constr:(
             {| phase1_static_argument_spine_tag := Phase1StaticEffectSetArgument;
                phase1_static_argument_spine_selected_tree := selected |}) in
           assert (Hnormalize :
             phase1_surface_normalize_static_argument_spine tree = Some argument).
           {
             rewrite Htree, Hsubtree.
             unfold phase1_surface_normalize_static_argument_spine,
               phase1_surface_expect_nonterminal,
               phase1_surface_expect_alternative,
               phase1_surface_validate_static_argument_selected,
               phase1_surface_static_argument_tag_name.
             cbn.
             rewrite Hvalidate.
             reflexivity.
           }
           exists argument.
           split.
           ++ exact Hnormalize.
           ++ eapply phase1_surface_normalize_static_argument_spine_round_trip.
              exact Hnormalize.
        -- cbn in Hnth.
           discriminate Hnth.
Qed.

Lemma phase1_surface_normalize_static_argument_suffix_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_static_argument_suffix_expression_for_totality
      input rest tree ->
    exists argument,
      phase1_surface_normalize_static_argument_suffix tree = Some argument /\
      phase1_surface_static_argument_suffix_tree argument = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_static_argument_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral ",";
        ENonterminal "static_argument"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hcomma : Derives phase1_surface_rules _
      (ELiteral ",") _ _ ?comma_tree,
    Hargument : Derives phase1_surface_rules _
      (ENonterminal "static_argument") _ _ ?argument_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "," _ _ comma_tree Hcomma)
        as [comma_tail [_ [_ Hcomma_tree]]];
      destruct
        (phase1_surface_normalize_static_argument_spine_total_from_derivation
          _ _ _ argument_tree Hargument)
        as [argument [Hargument_normalize Hargument_round_trip]];
      assert (Hnormalize :
        phase1_surface_normalize_static_argument_suffix tree = Some argument);
      [ rewrite Htree, Hcomma_tree;
        unfold phase1_surface_normalize_static_argument_suffix,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_literal;
        cbn;
        rewrite Hargument_normalize;
        reflexivity
      | exists argument;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_static_argument_suffix_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_static_argument_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_static_argument_suffix_expression_for_totality ->
    exists arguments,
      phase1_surface_normalize_static_argument_suffixes trees = Some arguments.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [].
    reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_static_argument_suffix_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [argument [Hargument Hargument_round_trip]].
    destruct (IHrest eq_refl) as [arguments Harguments].
    exists (argument :: arguments).
    cbn.
    rewrite Hargument.
    rewrite Harguments.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_static_argument_list_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_static_argument_list_expression_for_totality
      input rest tree ->
    exists arguments,
      phase1_surface_normalize_static_argument_list_spine tree = Some arguments /\
      phase1_surface_static_argument_list_spine_tree arguments = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_static_argument_list_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ENonterminal "static_argument";
        ERepetition phase1_surface_static_argument_suffix_expression_for_totality
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hfirst : Derives phase1_surface_rules _
      (ENonterminal "static_argument") _ _ ?first_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_static_argument_suffix_expression_for_totality)
      _ _ ?rest_tree |- _ =>
      destruct
        (phase1_surface_normalize_static_argument_spine_total_from_derivation
          _ _ _ first_tree Hfirst)
        as [first [Hfirst_normalize Hfirst_round_trip]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_static_argument_suffix_expression_for_totality
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_body]];
      destruct
        (phase1_surface_normalize_static_argument_suffixes_total_from_repetition
          _ phase1_surface_static_argument_suffix_expression_for_totality
          _ _ rest_trees Hrest_body eq_refl)
        as [rest_arguments Hrest_normalize];
      let arguments := constr:(
        {| phase1_static_argument_list_spine_first := first;
           phase1_static_argument_list_spine_rest := rest_arguments |}) in
      assert (Hnormalize :
        phase1_surface_normalize_static_argument_list_spine tree = Some arguments);
      [ rewrite Htree, Hrest_tree;
        unfold phase1_surface_normalize_static_argument_list_spine,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_repetition;
        cbn;
        rewrite Hfirst_normalize;
        rewrite Hrest_normalize;
        reflexivity
      | exists arguments;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_static_argument_list_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_optional_static_argument_list_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_optional_static_argument_list_expression_for_totality
      input rest tree ->
    exists arguments,
      phase1_surface_normalize_optional_static_argument_list tree = Some arguments /\
      phase1_surface_optional_static_argument_list_tree arguments = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_optional_static_argument_list_expression_for_totality in Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      phase1_surface_static_argument_list_expression_for_totality
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_static_argument_list tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_static_argument_list_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_static_argument_list_spine_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [arguments [Harguments Harguments_round_trip]].
    assert (Hnormalize :
      phase1_surface_normalize_optional_static_argument_list tree =
        Some (Some arguments)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_static_argument_list,
        phase1_surface_expect_optional.
      cbn.
      rewrite Harguments.
      reflexivity.
    }
    exists (Some arguments).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_static_argument_list_round_trip.
      exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_static_arguments_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "static_arguments")
      input rest tree ->
    exists arguments,
      phase1_surface_normalize_static_arguments_spine tree = Some arguments /\
      phase1_surface_static_arguments_spine_tree arguments = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "static_arguments"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_static_arguments_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  unfold phase1_surface_static_arguments_expression_for_totality in Hbody.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "static_arguments"))
      [ ELiteral "[";
        phase1_surface_optional_static_argument_list_expression_for_totality;
        ELiteral "]"
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
  | Hopen : Derives phase1_surface_rules _
      (ELiteral "[") _ _ ?open_tree,
    Harguments : Derives phase1_surface_rules _
      phase1_surface_optional_static_argument_list_expression_for_totality
      _ _ ?arguments_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "]") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "[" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (phase1_surface_normalize_optional_static_argument_list_total_from_derivation
          _ _ _ arguments_tree Harguments)
        as [argument_list [Harguments_normalize Harguments_round_trip]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "]" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      let arguments := constr:(
        {| phase1_static_arguments_spine_items := argument_list |}) in
      assert (Hnormalize :
        phase1_surface_normalize_static_arguments_spine tree = Some arguments);
      [ rewrite Htree, Hsubtree, Hopen_tree, Hclose_tree;
        unfold phase1_surface_normalize_static_arguments_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact3,
          phase1_surface_expect_literal;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Harguments_normalize;
        reflexivity
      | exists arguments;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_static_arguments_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
