From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStaticTypeArgumentCarrierSpine
  GrammarAstStaticTypeArgumentPayloadTotality
  GrammarAstStaticArgumentsCarrierTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the refined type-valued static-argument carrier lift from #991. *)

Lemma phase1_surface_normalize_static_type_argument_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "static_argument")
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_static_argument_spine tree = Some base /\
      phase1_surface_normalize_static_type_argument_spine base = Some refined /\
      phase1_surface_static_type_argument_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_static_argument_spine_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  destruct
    (phase1_surface_normalize_static_type_argument_tree_total_from_derivation
      path input rest tree Hderive)
    as [refined [Hrefined_tree Hrefined_round_trip]].
  assert (Hrefined :
    phase1_surface_normalize_static_type_argument_spine base = Some refined).
  {
    unfold phase1_surface_normalize_static_type_argument_tree in Hrefined_tree.
    rewrite Hbase in Hrefined_tree.
    exact Hrefined_tree.
  }
  exists base, refined.
  repeat split; assumption.
Qed.

Lemma phase1_surface_normalize_static_type_argument_suffix_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_static_argument_suffix_expression_for_totality
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_static_argument_suffix tree = Some base /\
      phase1_surface_normalize_static_type_argument_spine base = Some refined /\
      phase1_surface_static_type_argument_suffix_tree refined = tree.
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
        (phase1_surface_normalize_static_type_argument_layers_total_from_derivation
          _ _ _ argument_tree Hargument)
        as [base [refined [Hbase [Hrefined Hrefined_tree]]]];
      assert (Hsuffix :
        phase1_surface_normalize_static_argument_suffix tree = Some base);
      [ rewrite Htree, Hcomma_tree;
        unfold phase1_surface_normalize_static_argument_suffix,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_literal;
        cbn;
        rewrite Hbase;
        reflexivity
      | exists base, refined;
        split;
        [ exact Hsuffix
        | split;
          [ exact Hrefined
          | unfold phase1_surface_static_type_argument_suffix_tree;
            rewrite Htree, Hcomma_tree, Hrefined_tree;
            reflexivity ] ] ]
  end.
Qed.

Lemma phase1_surface_normalize_static_type_argument_suffixes_layers_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_static_argument_suffix_expression_for_totality ->
    exists bases refined,
      phase1_surface_normalize_static_argument_suffixes trees = Some bases /\
      phase1_surface_normalize_static_type_argument_values bases = Some refined.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [], [].
    split; reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_static_type_argument_suffix_layers_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [base [refined [Hbase [Hrefined Hrefined_tree]]]].
    destruct (IHrest eq_refl)
      as [bases [refined_rest [Hbases Hrefined_rest]]].
    exists (base :: bases), (refined :: refined_rest).
    split.
    + cbn.
      rewrite Hbase, Hbases.
      reflexivity.
    + cbn.
      rewrite Hrefined, Hrefined_rest.
      reflexivity.
Qed.

Lemma phase1_surface_normalize_static_type_argument_list_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_static_argument_list_expression_for_totality
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_static_argument_list_spine tree = Some base /\
      phase1_surface_normalize_static_type_argument_list_spine base = Some refined /\
      phase1_surface_static_type_argument_list_spine_tree refined = tree.
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
        (phase1_surface_normalize_static_type_argument_layers_total_from_derivation
          _ _ _ first_tree Hfirst)
        as [base_first [refined_first
            [Hbase_first [Hrefined_first Hrefined_first_tree]]]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_static_argument_suffix_expression_for_totality
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_body]];
      destruct
        (phase1_surface_normalize_static_type_argument_suffixes_layers_total_from_repetition
          _ phase1_surface_static_argument_suffix_expression_for_totality
          _ _ rest_trees Hrest_body eq_refl)
        as [base_rest [refined_rest [Hbase_rest Hrefined_rest]]];
      let base := constr:(
        {| phase1_static_argument_list_spine_first := base_first;
           phase1_static_argument_list_spine_rest := base_rest |}) in
      let refined := constr:(
        {| phase1_static_type_argument_list_spine_first := refined_first;
           phase1_static_type_argument_list_spine_rest := refined_rest |}) in
      assert (Hbase :
        phase1_surface_normalize_static_argument_list_spine tree = Some base);
      [ rewrite Htree, Hrest_tree;
        unfold phase1_surface_normalize_static_argument_list_spine,
          phase1_surface_expect_sequence,
          phase1_surface_exact2,
          phase1_surface_expect_repetition;
        cbn;
        rewrite Hbase_first, Hbase_rest;
        reflexivity
      | assert (Hrefined :
          phase1_surface_normalize_static_type_argument_list_spine base =
            Some refined);
        [ cbn;
          rewrite Hrefined_first, Hrefined_rest;
          reflexivity
        | exists base, refined;
          split;
          [ exact Hbase
          | split;
            [ exact Hrefined
            | transitivity (phase1_surface_static_argument_list_spine_tree base);
              [ eapply
                  phase1_surface_normalize_static_type_argument_list_spine_round_trip;
                exact Hrefined
              | eapply phase1_surface_normalize_static_argument_list_spine_round_trip;
                exact Hbase ] ] ] ] ]
  end.
Qed.

Lemma phase1_surface_normalize_optional_static_type_argument_list_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_optional_static_argument_list_expression_for_totality
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_optional_static_argument_list tree = Some base /\
      phase1_surface_normalize_optional_static_type_argument_list base = Some refined /\
      phase1_surface_optional_static_type_argument_list_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_optional_static_argument_list_expression_for_totality in Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      phase1_surface_static_argument_list_expression_for_totality
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - exists None, None.
    split.
    + rewrite Hnone.
      reflexivity.
    + split.
      * reflexivity.
      * rewrite Hnone.
        reflexivity.
  - destruct
      (phase1_surface_normalize_static_type_argument_list_layers_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [base [refined [Hbase [Hrefined Hrefined_tree]]]].
    assert (Hbase_optional :
      phase1_surface_normalize_optional_static_argument_list tree =
        Some (Some base)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_static_argument_list,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hbase.
      reflexivity.
    }
    assert (Hrefined_optional :
      phase1_surface_normalize_optional_static_type_argument_list (Some base) =
        Some (Some refined)).
    {
      cbn.
      rewrite Hrefined.
      reflexivity.
    }
    exists (Some base), (Some refined).
    split.
    + exact Hbase_optional.
    + split.
      * exact Hrefined_optional.
      * rewrite Hsome.
        cbn.
        exact (f_equal PTOptionalSome Hrefined_tree).
Qed.

Lemma phase1_surface_normalize_static_type_arguments_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "static_arguments")
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_static_arguments_spine tree = Some base /\
      phase1_surface_normalize_static_type_arguments_spine base = Some refined /\
      phase1_surface_static_type_arguments_spine_tree refined = tree.
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
        (phase1_surface_normalize_optional_static_type_argument_list_layers_total_from_derivation
          _ _ _ arguments_tree Harguments)
        as [base_items [refined_items
            [Hbase_items [Hrefined_items Hrefined_items_tree]]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "]" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      let base := constr:(
        {| phase1_static_arguments_spine_items := base_items |}) in
      let refined := constr:(
        {| phase1_static_type_arguments_spine_items := refined_items |}) in
      assert (Hbase :
        phase1_surface_normalize_static_arguments_spine tree = Some base);
      [ rewrite Htree, Hsubtree, Hopen_tree, Hclose_tree;
        unfold phase1_surface_normalize_static_arguments_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact3,
          phase1_surface_expect_literal;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Hbase_items;
        reflexivity
      | assert (Hrefined :
          phase1_surface_normalize_static_type_arguments_spine base = Some refined);
        [ cbn;
          rewrite Hrefined_items;
          reflexivity
        | exists base, refined;
          split;
          [ exact Hbase
          | split;
            [ exact Hrefined
            | transitivity (phase1_surface_static_arguments_spine_tree base);
              [ eapply
                  phase1_surface_normalize_static_type_arguments_spine_round_trip;
                exact Hrefined
              | eapply phase1_surface_normalize_static_arguments_spine_round_trip;
                exact Hbase ] ] ] ] ]
  end.
Qed.

Lemma phase1_surface_normalize_static_type_arguments_reference_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "static_reference")
      input rest tree ->
    exists base middle refined,
      phase1_surface_normalize_static_reference_spine tree = Some base /\
      phase1_surface_normalize_static_arguments_reference_spine base = Some middle /\
      phase1_surface_normalize_static_type_arguments_reference_spine middle =
        Some refined /\
      phase1_surface_static_type_arguments_reference_spine_tree refined = tree.
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
  inversion Hitems as
    [| path0 index0 item0 items0 input0 middle0 rest0
       name_tree tail1 Hname Htail1]; subst.
  inversion Htail1 as
    [| path1 index1 item1 items1 input1 middle1 rest1
       arguments_tree nil_trees Harguments Hnil]; subst.
  inversion Hnil; subst.
  destruct
    (phase1_surface_normalize_qualified_name_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules _
      (ENonterminal "static_arguments")
      _ _ arguments_tree Harguments)
    as [[_ Hnone] | [arguments_body [Hsome Harguments_body]]].
  - let base := constr:(
      {| phase1_static_reference_spine_name := name;
         phase1_static_reference_spine_arguments := None |}) in
    let middle := constr:(
      {| phase1_static_arguments_reference_spine_name := name;
         phase1_static_arguments_reference_spine_arguments := None |}) in
    let refined := constr:(
      {| phase1_static_type_arguments_reference_spine_name := name;
         phase1_static_type_arguments_reference_spine_arguments := None |}) in
    assert (Hbase :
      phase1_surface_normalize_static_reference_spine tree = Some base).
    {
      rewrite Htree, Hsubtree, Hnone.
      unfold phase1_surface_normalize_static_reference_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_normalize_optional_static_arguments,
        phase1_surface_expect_optional.
      cbn.
      rewrite String.eqb_refl.
      rewrite Hname_normalize.
      reflexivity.
    }
    assert (Hmiddle :
      phase1_surface_normalize_static_arguments_reference_spine base =
        Some middle).
    { reflexivity. }
    assert (Hrefined :
      phase1_surface_normalize_static_type_arguments_reference_spine middle =
        Some refined).
    { reflexivity. }
    exists base, middle, refined.
    repeat split; try assumption.
    transitivity (phase1_surface_static_arguments_reference_spine_tree middle).
    + eapply
        phase1_surface_normalize_static_type_arguments_reference_spine_round_trip.
      exact Hrefined.
    + transitivity (phase1_surface_static_reference_spine_tree base).
      * eapply
          phase1_surface_normalize_static_arguments_reference_spine_round_trip.
        exact Hmiddle.
      * eapply phase1_surface_normalize_static_reference_spine_round_trip.
        exact Hbase.
  - pose proof
      (phase1_surface_validate_named_node_total_from_derivation
        "static_arguments" _ _ _ arguments_body Harguments_body)
      as Hvalidate.
    destruct
      (phase1_surface_normalize_static_type_arguments_layers_total_from_derivation
        _ _ _ arguments_body Harguments_body)
      as [base_arguments [refined_arguments
          [Hbase_arguments [Hrefined_arguments Harguments_round_trip]]]].
    let base := constr:(
      {| phase1_static_reference_spine_name := name;
         phase1_static_reference_spine_arguments := Some arguments_body |}) in
    let middle := constr:(
      {| phase1_static_arguments_reference_spine_name := name;
         phase1_static_arguments_reference_spine_arguments :=
           Some base_arguments |}) in
    let refined := constr:(
      {| phase1_static_type_arguments_reference_spine_name := name;
         phase1_static_type_arguments_reference_spine_arguments :=
           Some refined_arguments |}) in
    assert (Hbase :
      phase1_surface_normalize_static_reference_spine tree = Some base).
    {
      rewrite Htree, Hsubtree, Hsome.
      unfold phase1_surface_normalize_static_reference_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_sequence,
        phase1_surface_exact2,
        phase1_surface_normalize_optional_static_arguments,
        phase1_surface_expect_optional.
      cbn.
      rewrite String.eqb_refl.
      rewrite Hname_normalize.
      unfold phase1_surface_validate_named_node in Hvalidate |- *.
      rewrite Hvalidate.
      reflexivity.
    }
    assert (Hmiddle :
      phase1_surface_normalize_static_arguments_reference_spine base =
        Some middle).
    {
      cbn.
      rewrite Hbase_arguments.
      reflexivity.
    }
    assert (Hrefined :
      phase1_surface_normalize_static_type_arguments_reference_spine middle =
        Some refined).
    {
      cbn.
      rewrite Hrefined_arguments.
      reflexivity.
    }
    exists base, middle, refined.
    repeat split; try assumption.
    transitivity (phase1_surface_static_arguments_reference_spine_tree middle).
    + eapply
        phase1_surface_normalize_static_type_arguments_reference_spine_round_trip.
      exact Hrefined.
    + transitivity (phase1_surface_static_reference_spine_tree base).
      * eapply
          phase1_surface_normalize_static_arguments_reference_spine_round_trip.
        exact Hmiddle.
      * eapply phase1_surface_normalize_static_reference_spine_round_trip.
        exact Hbase.
Qed.

Theorem phase1_surface_normalize_static_type_arguments_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "type_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_static_type_arguments_type_tree tree = Some refined /\
      phase1_surface_static_type_arguments_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "type_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_type_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "type_expression"))
      phase1_surface_type_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_refinement_tuple_nonreference_total_from_derivation
        (descend
          (descend path (AtNonterminal "type_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [type_value [primitive [shallow [nonreference
          [Houter [Hprimitive [Hshallow [Hrefine Hround]]]]]]]].
    let outer_type := constr:(Phase1NonreferenceTypeSpine type_value) in
    let primitive_type := constr:(Phase1PrimitiveNonreferenceTypeSpine primitive) in
    let shallow_type := constr:(Phase1ShallowCompoundNonreferenceTypeSpine shallow) in
    let refinement_type := constr:(Phase1RefinementTupleNonreferenceTypeSpine nonreference) in
    let static_reference_type := constr:(Phase1StaticReferenceNonreferenceType nonreference) in
    let static_arguments_type := constr:(Phase1StaticArgumentsNonreferenceType nonreference) in
    let result := constr:(Phase1StaticTypeArgumentsNonreferenceType nonreference) in
    assert (Htype :
      phase1_surface_normalize_type_spine tree = Some outer_type).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_type_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite String.eqb_refl.
      rewrite Houter.
      reflexivity.
    }
    assert (Hprimitive_type :
      phase1_surface_normalize_primitive_type_tree tree = Some primitive_type).
    {
      unfold phase1_surface_normalize_primitive_type_tree.
      rewrite Htype.
      cbn.
      rewrite Hprimitive.
      reflexivity.
    }
    assert (Hshallow_type :
      phase1_surface_normalize_shallow_compound_type_tree tree = Some shallow_type).
    {
      unfold phase1_surface_normalize_shallow_compound_type_tree.
      rewrite Hprimitive_type.
      cbn.
      rewrite Hshallow.
      reflexivity.
    }
    assert (Hrefinement_type :
      phase1_surface_normalize_refinement_tuple_type_tree tree =
        Some refinement_type).
    {
      unfold phase1_surface_normalize_refinement_tuple_type_tree.
      rewrite Hshallow_type.
      cbn.
      rewrite Hrefine.
      reflexivity.
    }
    assert (Hstatic_reference_type :
      phase1_surface_normalize_static_reference_type_tree tree =
        Some static_reference_type).
    {
      unfold phase1_surface_normalize_static_reference_type_tree.
      rewrite Hrefinement_type.
      reflexivity.
    }
    assert (Hstatic_arguments_type :
      phase1_surface_normalize_static_arguments_type_tree tree =
        Some static_arguments_type).
    {
      unfold phase1_surface_normalize_static_arguments_type_tree.
      rewrite Hstatic_reference_type.
      reflexivity.
    }
    assert (Hresult :
      phase1_surface_normalize_static_type_arguments_type_tree tree = Some result).
    {
      unfold phase1_surface_normalize_static_type_arguments_type_tree.
      rewrite Hstatic_arguments_type.
      reflexivity.
    }
    exists result.
    split.
    + exact Hresult.
    + eapply phase1_surface_normalize_static_type_arguments_type_tree_round_trip.
      exact Hresult.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (derives_nonterminal_exposes_body
          phase1_surface_rules
          (descend
            (descend path (AtNonterminal "type_expression"))
            (AtAlternative 1))
          "named_type" input rest selected Hselected)
        as [named_body [reference_tree
            [Hnamed_lookup [Hnamed_tree Hreference]]]].
      rewrite phase1_surface_named_type_lookup_for_totality in Hnamed_lookup.
      inversion Hnamed_lookup; subst named_body.
      destruct
        (phase1_surface_normalize_static_type_arguments_reference_layers_total_from_derivation
          _ _ _ reference_tree Hreference)
        as [base_reference [middle_reference [refined_reference
            [Hbase_reference
             [Hmiddle_reference [Hrefined_reference Hreference_round_trip]]]]]].
      assert (Hnamed :
        phase1_surface_normalize_named_type_spine selected =
          Some base_reference).
      {
        rewrite Hnamed_tree.
        unfold phase1_surface_normalize_named_type_spine,
          phase1_surface_expect_nonterminal.
        cbn.
        rewrite String.eqb_refl.
        exact Hbase_reference.
      }
      let outer_type := constr:(Phase1NamedTypeSpine selected) in
      let primitive_type := constr:(Phase1PrimitiveNamedTypeSpine selected) in
      let shallow_type := constr:(Phase1ShallowCompoundNamedTypeSpine selected) in
      let refinement_type := constr:(Phase1RefinementTupleNamedTypeSpine selected) in
      let static_reference_type := constr:(Phase1StaticReferenceNamedType base_reference) in
      let static_arguments_type := constr:(Phase1StaticArgumentsNamedType middle_reference) in
      let result := constr:(Phase1StaticTypeArgumentsNamedType refined_reference) in
      assert (Htype :
        phase1_surface_normalize_type_spine tree = Some outer_type).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_type_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        rewrite String.eqb_refl.
        reflexivity.
      }
      assert (Hprimitive_type :
        phase1_surface_normalize_primitive_type_tree tree = Some primitive_type).
      {
        unfold phase1_surface_normalize_primitive_type_tree.
        rewrite Htype.
        reflexivity.
      }
      assert (Hshallow_type :
        phase1_surface_normalize_shallow_compound_type_tree tree = Some shallow_type).
      {
        unfold phase1_surface_normalize_shallow_compound_type_tree.
        rewrite Hprimitive_type.
        reflexivity.
      }
      assert (Hrefinement_type :
        phase1_surface_normalize_refinement_tuple_type_tree tree =
          Some refinement_type).
      {
        unfold phase1_surface_normalize_refinement_tuple_type_tree.
        rewrite Hshallow_type.
        reflexivity.
      }
      assert (Hstatic_reference_type :
        phase1_surface_normalize_static_reference_type_tree tree =
          Some static_reference_type).
      {
        unfold phase1_surface_normalize_static_reference_type_tree.
        rewrite Hrefinement_type.
        cbn.
        rewrite Hnamed.
        reflexivity.
      }
      assert (Hstatic_arguments_type :
        phase1_surface_normalize_static_arguments_type_tree tree =
          Some static_arguments_type).
      {
        unfold phase1_surface_normalize_static_arguments_type_tree.
        rewrite Hstatic_reference_type.
        cbn.
        rewrite Hmiddle_reference.
        reflexivity.
      }
      assert (Hresult :
        phase1_surface_normalize_static_type_arguments_type_tree tree = Some result).
      {
        unfold phase1_surface_normalize_static_type_arguments_type_tree.
        rewrite Hstatic_arguments_type.
        cbn.
        rewrite Hrefined_reference.
        reflexivity.
      }
      exists result.
      split.
      * exact Hresult.
      * eapply phase1_surface_normalize_static_type_arguments_type_tree_round_trip.
        exact Hresult.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
