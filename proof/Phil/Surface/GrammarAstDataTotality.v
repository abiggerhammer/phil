From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstVariantPayloadSpine
  GrammarAstRecordFieldsTotality
  GrammarAstGenericRequirementsTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the staged data/variant/payload correspondence introduced by
   #952, #954, and #955. *)

Definition phase1_surface_tuple_type_suffix_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral ",";
      ENonterminal "type_expression"
    ].

Definition phase1_surface_tuple_type_list_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ENonterminal "type_expression";
      ERepetition phase1_surface_tuple_type_suffix_expression_for_totality
    ].

Definition phase1_surface_optional_tuple_types_expression_for_totality
  : EbnfExpression :=
  EOptional phase1_surface_tuple_type_list_expression_for_totality.

Definition phase1_surface_record_variant_payload_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "{";
      phase1_surface_optional_fields_expression_for_totality;
      ELiteral "}"
    ].

Definition phase1_surface_tuple_variant_payload_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "(";
      phase1_surface_optional_tuple_types_expression_for_totality;
      ELiteral ")"
    ].

Definition phase1_surface_variant_payload_items_for_totality
  : list EbnfExpression :=
  [ phase1_surface_record_variant_payload_expression_for_totality;
    phase1_surface_tuple_variant_payload_expression_for_totality
  ].

Definition phase1_surface_data_variant_suffix_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "|";
      ENonterminal "variant_decl"
    ].

Lemma phase1_surface_variant_payload_lookup_for_totality :
  lookupRule "variant_payload" phase1_surface_rules =
    Some (EAlternative phase1_surface_variant_payload_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_variant_decl_lookup_for_totality :
  lookupRule "variant_decl" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "identifier";
          EOptional (ENonterminal "variant_payload")
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_data_decl_lookup_for_totality :
  lookupRule "data_decl" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "data";
          ENonterminal "identifier";
          EOptional (ENonterminal "generic_params");
          EOptional
            (ESequence
              [ ELiteral "mode";
                ENonterminal "structural_mode"
              ]);
          EOptional (ENonterminal "generic_requirements");
          ELiteral "=";
          ENonterminal "variant_decl";
          ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
          ELiteral ";"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_tuple_type_suffix_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_tuple_type_suffix_expression_for_totality
      input rest tree ->
    exists type_tree,
      phase1_surface_normalize_tuple_type_suffix tree = Some type_tree /\
      phase1_surface_tuple_type_suffix_tree type_tree = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_tuple_type_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral ",";
        ENonterminal "type_expression"
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
    Htype : Derives phase1_surface_rules _
      (ENonterminal "type_expression") _ _ ?type_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "," _ _ comma_tree Hcomma)
        as [comma_tail [_ [_ Hcomma_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "type_expression" _ _ _ type_tree Htype) as Htype_validate;
      assert (Hnormalize :
        phase1_surface_normalize_tuple_type_suffix tree = Some type_tree);
      [ rewrite Htree, Hcomma_tree;
        unfold phase1_surface_normalize_tuple_type_suffix,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_literal;
        cbn;
        rewrite Htype_validate;
        reflexivity
      | exists type_tree;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_tuple_type_suffix_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_tuple_type_suffixes_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_tuple_type_suffix_expression_for_totality ->
    exists types,
      phase1_surface_normalize_tuple_type_suffixes trees = Some types.
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
      (phase1_surface_normalize_tuple_type_suffix_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [type_tree [Htree Htree_round_trip]].
    destruct (IHrest eq_refl) as [types Htypes].
    exists (type_tree :: types).
    cbn.
    rewrite Htree.
    rewrite Htypes.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_tuple_type_list_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_tuple_type_list_expression_for_totality
      input rest tree ->
    exists types,
      phase1_surface_normalize_tuple_type_list_spine tree = Some types /\
      phase1_surface_tuple_type_list_spine_tree types = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_tuple_type_list_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ENonterminal "type_expression";
        ERepetition phase1_surface_tuple_type_suffix_expression_for_totality
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
      (ENonterminal "type_expression") _ _ ?first_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_tuple_type_suffix_expression_for_totality)
      _ _ ?rest_tree |- _ =>
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "type_expression" _ _ _ first_tree Hfirst) as Hfirst_validate;
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_tuple_type_suffix_expression_for_totality
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_body]];
      destruct
        (phase1_surface_normalize_tuple_type_suffixes_total_from_repetition
          _ phase1_surface_tuple_type_suffix_expression_for_totality
          _ _ rest_trees Hrest_body eq_refl)
        as [rest_types Hrest_normalize];
      let types := constr:(
        {| phase1_tuple_type_list_spine_first := first_tree;
           phase1_tuple_type_list_spine_rest := rest_types |}) in
      assert (Hnormalize :
        phase1_surface_normalize_tuple_type_list_spine tree = Some types);
      [ rewrite Htree, Hrest_tree;
        unfold phase1_surface_normalize_tuple_type_list_spine,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_repetition;
        cbn;
        rewrite Hfirst_validate;
        rewrite Hrest_normalize;
        reflexivity
      | exists types;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_tuple_type_list_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_optional_tuple_types_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_optional_tuple_types_expression_for_totality
      input rest tree ->
    exists types,
      phase1_surface_normalize_optional_tuple_types tree = Some types /\
      phase1_surface_optional_tuple_types_tree types = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_optional_tuple_types_expression_for_totality in Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      phase1_surface_tuple_type_list_expression_for_totality
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_tuple_types tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_tuple_types_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_tuple_type_list_spine_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [types [Htypes Htypes_round_trip]].
    assert (Hnormalize :
      phase1_surface_normalize_optional_tuple_types tree = Some (Some types)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_tuple_types,
        phase1_surface_expect_optional.
      cbn.
      rewrite Htypes.
      reflexivity.
    }
    exists (Some types).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_tuple_types_round_trip.
      exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_record_variant_payload_selected_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_record_variant_payload_expression_for_totality
      input rest tree ->
    exists payload,
      phase1_surface_normalize_record_variant_payload_selected tree = Some payload /\
      phase1_surface_variant_payload_spine_index payload = 0 /\
      phase1_surface_variant_payload_selected_tree payload = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_record_variant_payload_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "{";
        phase1_surface_optional_fields_expression_for_totality;
        ELiteral "}"
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
  | Hopen : Derives phase1_surface_rules _
      (ELiteral "{") _ _ ?open_tree,
    Hfields : Derives phase1_surface_rules _
      phase1_surface_optional_fields_expression_for_totality _ _ ?fields_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "}") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "{" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "}" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (phase1_surface_normalize_optional_fields_total_from_derivation
          _ _ _ fields_tree Hfields)
        as [fields [Hfields_normalize Hfields_round_trip]];
      let payload := constr:(Phase1VariantRecordPayloadSpine fields) in
      assert (Hnormalize :
        phase1_surface_normalize_record_variant_payload_selected tree =
          Some payload);
      [ rewrite Htree, Hopen_tree, Hclose_tree;
        unfold phase1_surface_normalize_record_variant_payload_selected,
          phase1_surface_expect_sequence,
          phase1_surface_exact3,
          phase1_surface_expect_literal;
        cbn;
        rewrite Hfields_normalize;
        reflexivity
      | exists payload;
        split;
        [ exact Hnormalize
        | destruct
            (phase1_surface_normalize_record_variant_payload_selected_round_trip
              tree payload Hnormalize)
            as [Hindex Hround];
          split; assumption ] ]
  end.
Qed.

Lemma phase1_surface_normalize_tuple_variant_payload_selected_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_tuple_variant_payload_expression_for_totality
      input rest tree ->
    exists payload,
      phase1_surface_normalize_tuple_variant_payload_selected tree = Some payload /\
      phase1_surface_variant_payload_spine_index payload = 1 /\
      phase1_surface_variant_payload_selected_tree payload = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_tuple_variant_payload_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "(";
        phase1_surface_optional_tuple_types_expression_for_totality;
        ELiteral ")"
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
  | Hopen : Derives phase1_surface_rules _
      (ELiteral "(") _ _ ?open_tree,
    Htypes : Derives phase1_surface_rules _
      phase1_surface_optional_tuple_types_expression_for_totality _ _ ?types_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral ")") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "(" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ")" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (phase1_surface_normalize_optional_tuple_types_total_from_derivation
          _ _ _ types_tree Htypes)
        as [types [Htypes_normalize Htypes_round_trip]];
      let payload := constr:(Phase1VariantTuplePayloadSpine types) in
      assert (Hnormalize :
        phase1_surface_normalize_tuple_variant_payload_selected tree =
          Some payload);
      [ rewrite Htree, Hopen_tree, Hclose_tree;
        unfold phase1_surface_normalize_tuple_variant_payload_selected,
          phase1_surface_expect_sequence,
          phase1_surface_exact3,
          phase1_surface_expect_literal;
        cbn;
        rewrite Htypes_normalize;
        reflexivity
      | exists payload;
        split;
        [ exact Hnormalize
        | destruct
            (phase1_surface_normalize_tuple_variant_payload_selected_round_trip
              tree payload Hnormalize)
            as [Hindex Hround];
          split; assumption ] ]
  end.
Qed.

Lemma phase1_surface_normalize_variant_payload_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "variant_payload")
      input rest tree ->
    exists payload,
      phase1_surface_normalize_variant_payload_spine tree = Some payload /\
      phase1_surface_variant_payload_spine_tree payload = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "variant_payload"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_variant_payload_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "variant_payload"))
      phase1_surface_variant_payload_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_record_variant_payload_selected_total_from_derivation
        _ _ _ selected Hselected)
      as [payload [Hselected_normalize [Hindex Hselected_round]]].
    assert (Hnormalize :
      phase1_surface_normalize_variant_payload_spine tree = Some payload).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_variant_payload_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hselected_normalize.
      reflexivity.
    }
    exists payload.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_variant_payload_spine_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_tuple_variant_payload_selected_total_from_derivation
          _ _ _ selected Hselected)
        as [payload [Hselected_normalize [Hindex Hselected_round]]].
      assert (Hnormalize :
        phase1_surface_normalize_variant_payload_spine tree = Some payload).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_variant_payload_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        rewrite Hselected_normalize.
        reflexivity.
      }
      exists payload.
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_variant_payload_spine_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.

Lemma phase1_surface_normalize_variant_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "variant_decl")
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_variant_spine tree = Some base /\
      phase1_surface_normalize_variant_payload_variant_spine base = Some refined /\
      phase1_surface_variant_payload_variant_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "variant_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_variant_decl_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "variant_decl"))
      [ ENonterminal "identifier";
        EOptional (ENonterminal "variant_payload")
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
      (ENonterminal "identifier") _ _ ?name_tree,
    Hpayload : Derives phase1_surface_rules _
      (EOptional (ENonterminal "variant_payload")) _ _ ?payload_tree |- _ =>
      destruct
        (phase1_surface_normalize_identifier_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize];
      destruct
        (optional_derivation_exposes_presence
          phase1_surface_rules _
          (ENonterminal "variant_payload")
          _ _ payload_tree Hpayload)
        as [[_ Hnone] | [payload_body [Hsome Hpayload_body]]];
      [ let base := constr:(
          {| phase1_variant_spine_name := name;
             phase1_variant_spine_payload := None |}) in
        let refined := constr:(
          {| phase1_variant_payload_variant_spine_name := name;
             phase1_variant_payload_variant_spine_payload := None |}) in
        assert (Hbase :
          phase1_surface_normalize_variant_spine tree = Some base);
        [ rewrite Htree, Hsubtree, Hnone;
          unfold phase1_surface_normalize_variant_spine,
            phase1_surface_expect_nonterminal,
            phase1_surface_expect_sequence,
            phase1_surface_exact2,
            phase1_surface_normalize_optional_variant_payload,
            phase1_surface_expect_optional;
          cbn;
          rewrite Hname_normalize;
          reflexivity
        | assert (Hrefined :
            phase1_surface_normalize_variant_payload_variant_spine base =
              Some refined);
          [ reflexivity
          | exists base, refined;
            repeat split;
            try assumption;
            transitivity (phase1_surface_variant_spine_tree base);
            [ eapply phase1_surface_normalize_variant_payload_variant_spine_round_trip;
              exact Hrefined
            | eapply phase1_surface_normalize_variant_spine_round_trip;
              exact Hbase ] ] ]
      | pose proof
          (phase1_surface_validate_named_node_total_from_derivation
            "variant_payload" _ _ _ payload_body Hpayload_body)
          as Hpayload_validate;
        destruct
          (phase1_surface_normalize_variant_payload_spine_total_from_derivation
            _ _ _ payload_body Hpayload_body)
          as [payload [Hpayload_normalize Hpayload_round_trip]];
        let base := constr:(
          {| phase1_variant_spine_name := name;
             phase1_variant_spine_payload := Some payload_body |}) in
        let refined := constr:(
          {| phase1_variant_payload_variant_spine_name := name;
             phase1_variant_payload_variant_spine_payload := Some payload |}) in
        assert (Hbase :
          phase1_surface_normalize_variant_spine tree = Some base);
        [ rewrite Htree, Hsubtree, Hsome;
          unfold phase1_surface_normalize_variant_spine,
            phase1_surface_expect_nonterminal,
            phase1_surface_expect_sequence,
            phase1_surface_exact2,
            phase1_surface_normalize_optional_variant_payload,
            phase1_surface_expect_optional;
          cbn;
          rewrite Hname_normalize;
          rewrite Hpayload_validate;
          reflexivity
        | assert (Hrefined :
            phase1_surface_normalize_variant_payload_variant_spine base =
              Some refined);
          [ cbn;
            rewrite Hpayload_normalize;
            reflexivity
          | exists base, refined;
            repeat split;
            try assumption;
            transitivity (phase1_surface_variant_spine_tree base);
            [ eapply phase1_surface_normalize_variant_payload_variant_spine_round_trip;
              exact Hrefined
            | eapply phase1_surface_normalize_variant_spine_round_trip;
              exact Hbase ] ] ] ]
  end.
Qed.

Lemma phase1_surface_normalize_data_variant_suffix_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_data_variant_suffix_expression_for_totality
      input rest tree ->
    exists raw_variant base_variant refined_variant,
      phase1_surface_normalize_data_variant_suffix tree = Some raw_variant /\
      phase1_surface_normalize_variant_spine raw_variant = Some base_variant /\
      phase1_surface_normalize_variant_payload_variant_spine base_variant =
        Some refined_variant.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_data_variant_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "|";
        ENonterminal "variant_decl"
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
  | Hbar : Derives phase1_surface_rules _
      (ELiteral "|") _ _ ?bar_tree,
    Hvariant : Derives phase1_surface_rules _
      (ENonterminal "variant_decl") _ _ ?variant_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "|" _ _ bar_tree Hbar)
        as [bar_tail [_ [_ Hbar_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "variant_decl" _ _ _ variant_tree Hvariant) as Hvariant_validate;
      destruct
        (phase1_surface_normalize_variant_layers_total_from_derivation
          _ _ _ variant_tree Hvariant)
        as [base [refined [Hbase [Hrefined Hround_trip]]]];
      assert (Hraw :
        phase1_surface_normalize_data_variant_suffix tree = Some variant_tree);
      [ rewrite Htree, Hbar_tree;
        unfold phase1_surface_normalize_data_variant_suffix,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_literal;
        cbn;
        rewrite Hvariant_validate;
        reflexivity
      | exists variant_tree, base, refined;
        repeat split; assumption ]
  end.
Qed.

Lemma phase1_surface_normalize_data_variant_layers_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_data_variant_suffix_expression_for_totality ->
    exists raw_variants base_variants refined_variants,
      phase1_surface_normalize_data_variant_suffixes trees = Some raw_variants /\
      phase1_surface_normalize_variant_spines raw_variants = Some base_variants /\
      phase1_surface_normalize_variant_payload_variant_spines base_variants =
        Some refined_variants.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [], [], [].
    repeat split; reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_data_variant_suffix_layers_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [raw [base [refined [Hraw [Hbase Hrefined]]]]].
    destruct (IHrest eq_refl)
      as [raws [bases [refineds [Hraws [Hbases Hrefineds]]]]].
    exists (raw :: raws), (base :: bases), (refined :: refineds).
    repeat split.
    + cbn. rewrite Hraw, Hraws. reflexivity.
    + cbn. rewrite Hbase, Hbases. reflexivity.
    + cbn. rewrite Hrefined, Hrefineds. reflexivity.
Qed.

Theorem phase1_surface_normalize_data_variant_payload_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_data_variant_payload_tree tree = Some refined /\
      phase1_surface_data_variant_payload_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "data_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_data_decl_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "data_decl"))
      [ ELiteral "data";
        ENonterminal "identifier";
        EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence
            [ ELiteral "mode";
              ENonterminal "structural_mode"
            ]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "=";
        ENonterminal "variant_decl";
        ERepetition phase1_surface_data_variant_suffix_expression_for_totality;
        ELiteral ";"
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
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral "data") _ _ ?keyword_tree,
    Hname : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?name_tree,
    Hgeneric : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_params")) _ _ ?generic_tree,
    Hmode : Derives phase1_surface_rules _
      (EOptional
        (ESequence
          [ ELiteral "mode";
            ENonterminal "structural_mode"
          ])) _ _ ?mode_tree,
    Hrequirements : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_requirements")) _ _ ?requirements_tree,
    Hequals : Derives phase1_surface_rules _
      (ELiteral "=") _ _ ?equals_tree,
    Hfirst : Derives phase1_surface_rules _
      (ENonterminal "variant_decl") _ _ ?first_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_data_variant_suffix_expression_for_totality)
      _ _ ?rest_tree,
    Hterminator : Derives phase1_surface_rules _
      (ELiteral ";") _ _ ?terminator_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "data" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "=" _ _ equals_tree Hequals)
        as [equals_tail [_ [_ Hequals_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
        as [terminator_tail [_ [_ Hterminator_tree]]];
      destruct
        (phase1_surface_normalize_identifier_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize];
      destruct
        (phase1_surface_normalize_optional_generic_params_total_from_derivation
          _ _ _ generic_tree Hgeneric)
        as [generic_params [Hgeneric_normalize Hgeneric_round_trip]];
      destruct
        (phase1_surface_normalize_optional_mode_total_from_derivation
          _ _ _ mode_tree Hmode)
        as [mode [Hmode_normalize Hmode_round_trip]];
      destruct
        (phase1_surface_normalize_optional_generic_requirements_total_from_derivation
          _ _ _ requirements_tree Hrequirements)
        as [requirements [Hrequirements_normalize Hrequirements_round_trip]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "variant_decl" _ _ _ first_tree Hfirst) as Hfirst_validate;
      destruct
        (phase1_surface_normalize_variant_layers_total_from_derivation
          _ _ _ first_tree Hfirst)
        as [first_base [first_refined
          [Hfirst_base [Hfirst_refined Hfirst_round_trip]]]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_data_variant_suffix_expression_for_totality
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_body]];
      destruct
        (phase1_surface_normalize_data_variant_layers_total_from_repetition
          _ phase1_surface_data_variant_suffix_expression_for_totality
          _ _ rest_trees Hrest_body eq_refl)
        as [raw_rest [base_rest [refined_rest
          [Hraw_rest [Hbase_rest Hrefined_rest]]]]];
      let raw_data := constr:(
        {| phase1_data_spine_name := name;
           phase1_data_spine_generic_params := generic_params;
           phase1_data_spine_mode := mode;
           phase1_data_spine_requirements := requirements;
           phase1_data_spine_first_variant_tree := first_tree;
           phase1_data_spine_rest_variant_trees := raw_rest |}) in
      let base_data := constr:(
        {| phase1_data_variant_spine_name := name;
           phase1_data_variant_spine_generic_params := generic_params;
           phase1_data_variant_spine_mode := mode;
           phase1_data_variant_spine_requirements := requirements;
           phase1_data_variant_spine_first_variant := first_base;
           phase1_data_variant_spine_rest_variants := base_rest |}) in
      let refined_data := constr:(
        {| phase1_data_variant_payload_spine_name := name;
           phase1_data_variant_payload_spine_generic_params := generic_params;
           phase1_data_variant_payload_spine_mode := mode;
           phase1_data_variant_payload_spine_requirements := requirements;
           phase1_data_variant_payload_spine_first_variant := first_refined;
           phase1_data_variant_payload_spine_rest_variants := refined_rest |}) in
      assert (Hraw_data :
        phase1_surface_normalize_data_spine tree = Some raw_data).
      {
        rewrite Htree, Hsubtree, Hkeyword_tree,
          Hequals_tree, Hrest_tree, Hterminator_tree.
        unfold phase1_surface_normalize_data_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact9,
          phase1_surface_expect_literal,
          phase1_surface_expect_repetition.
        cbn.
        rewrite Hfirst_validate.
        rewrite Hname_normalize.
        rewrite Hgeneric_normalize.
        rewrite Hmode_normalize.
        rewrite Hrequirements_normalize.
        rewrite Hraw_rest.
        reflexivity.
      }
      assert (Hbase_data :
        phase1_surface_normalize_data_variant_spine raw_data = Some base_data).
      {
        unfold phase1_surface_normalize_data_variant_spine.
        cbn.
        rewrite Hfirst_base.
        rewrite Hbase_rest.
        reflexivity.
      }
      assert (Hrefined_data :
        phase1_surface_normalize_data_variant_payload_spine base_data =
          Some refined_data).
      {
        unfold phase1_surface_normalize_data_variant_payload_spine.
        cbn.
        rewrite Hfirst_refined.
        rewrite Hrefined_rest.
        reflexivity.
      }
      assert (Hbase_tree :
        phase1_surface_normalize_data_variant_tree tree = Some base_data).
      {
        unfold phase1_surface_normalize_data_variant_tree.
        rewrite Hraw_data.
        exact Hbase_data.
      }
      assert (Hnormalize :
        phase1_surface_normalize_data_variant_payload_tree tree =
          Some refined_data).
      {
        unfold phase1_surface_normalize_data_variant_payload_tree.
        rewrite Hbase_tree.
        exact Hrefined_data.
      }
      exists refined_data.
      split.
      + exact Hnormalize.
      + eapply phase1_surface_normalize_data_variant_payload_tree_round_trip.
        exact Hnormalize
  end.
Qed.
