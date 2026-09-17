From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstFieldTypeListSpine
  GrammarAstFieldTypeTotality
  GrammarAstRecordFieldsTotality.

Import ListNotations.

(* Converse for the field-list type refinement from #1163. *)

Lemma phase1_surface_normalize_field_type_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "field_decl")
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_field_spine tree = Some base /\
      phase1_surface_normalize_field_type_spine base = Some refined /\
      phase1_surface_field_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_field_spine_total_from_derivation
      path input rest tree Hderive)
    as [base [Hbase Hbase_round_trip]].
  destruct
    (phase1_surface_normalize_field_type_tree_total_from_derivation
      path input rest tree Hderive)
    as [refined [Hrefined_tree Hrefined_round_trip]].
  assert (Hrefined :
    phase1_surface_normalize_field_type_spine base = Some refined).
  {
    unfold phase1_surface_normalize_field_type_tree in Hrefined_tree.
    rewrite Hbase in Hrefined_tree.
    exact Hrefined_tree.
  }
  exists base, refined.
  repeat split; assumption.
Qed.

Lemma phase1_surface_normalize_field_type_suffix_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_field_suffix_expression_for_totality
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_field_suffix tree = Some base /\
      phase1_surface_normalize_field_type_spine base = Some refined /\
      phase1_surface_field_type_suffix_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_field_suffix_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral ",";
        ENonterminal "field_decl"
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
    Hfield : Derives phase1_surface_rules _
      (ENonterminal "field_decl") _ _ ?field_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "," _ _ comma_tree Hcomma)
        as [comma_tail [_ [_ Hcomma_tree]]];
      destruct
        (phase1_surface_normalize_field_type_layers_total_from_derivation
          _ _ _ field_tree Hfield)
        as [base [refined [Hbase [Hrefined Hrefined_tree]]]];
      assert (Hsuffix :
        phase1_surface_normalize_field_suffix tree = Some base);
      [ rewrite Htree, Hcomma_tree;
        unfold phase1_surface_normalize_field_suffix,
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
          | unfold phase1_surface_field_type_suffix_tree;
            rewrite Htree, Hcomma_tree, Hrefined_tree;
            reflexivity ] ] ]
  end.
Qed.

Lemma phase1_surface_normalize_field_type_suffixes_layers_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = phase1_surface_field_suffix_expression_for_totality ->
    exists bases refined,
      phase1_surface_normalize_field_suffixes trees = Some bases /\
      phase1_surface_normalize_field_type_values bases = Some refined.
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
      (phase1_surface_normalize_field_type_suffix_layers_total_from_derivation
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

Theorem phase1_surface_normalize_field_type_list_layers_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_field_list_expression_for_totality
      input rest tree ->
    exists base refined,
      phase1_surface_normalize_field_list_spine tree = Some base /\
      phase1_surface_normalize_field_type_list_spine base = Some refined /\
      phase1_surface_field_type_list_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_field_list_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ENonterminal "field_decl";
        ERepetition phase1_surface_field_suffix_expression_for_totality;
        EOptional (ELiteral ",")
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
      (ENonterminal "field_decl") _ _ ?first_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_field_suffix_expression_for_totality)
      _ _ ?rest_tree,
    Htrailing : Derives phase1_surface_rules _
      (EOptional (ELiteral ",")) _ _ ?trailing_tree |- _ =>
      destruct
        (phase1_surface_normalize_field_type_layers_total_from_derivation
          _ _ _ first_tree Hfirst)
        as [base_first [refined_first
            [Hbase_first [Hrefined_first Hrefined_first_tree]]]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ phase1_surface_field_suffix_expression_for_totality
          _ _ rest_tree Hrest)
        as [rest_trees [Hrest_tree Hrest_body]];
      destruct
        (phase1_surface_normalize_field_type_suffixes_layers_total_from_repetition
          _ phase1_surface_field_suffix_expression_for_totality
          _ _ rest_trees Hrest_body eq_refl)
        as [base_rest [refined_rest [Hbase_rest Hrefined_rest]]];
      destruct
        (phase1_surface_normalize_trailing_comma_total_from_derivation
          _ _ _ trailing_tree Htrailing)
        as [trailing [Htrailing_normalize Htrailing_round_trip]];
      let base := constr:(
        {| phase1_field_list_spine_first := base_first;
           phase1_field_list_spine_rest := base_rest;
           phase1_field_list_spine_trailing_comma := trailing |}) in
      let refined := constr:(
        {| phase1_field_type_list_spine_first := refined_first;
           phase1_field_type_list_spine_rest := refined_rest;
           phase1_field_type_list_spine_trailing_comma := trailing |}) in
      assert (Hbase :
        phase1_surface_normalize_field_list_spine tree = Some base);
      [ rewrite Htree, Hrest_tree;
        unfold phase1_surface_normalize_field_list_spine,
          phase1_surface_expect_sequence,
          phase1_surface_exact3,
          phase1_surface_expect_repetition;
        cbn;
        rewrite Hbase_first;
        rewrite Htrailing_normalize;
        rewrite Hbase_rest;
        reflexivity
      | assert (Hrefined :
          phase1_surface_normalize_field_type_list_spine base = Some refined);
        [ cbn;
          rewrite Hrefined_first, Hrefined_rest;
          reflexivity
        | exists base, refined;
          split;
          [ exact Hbase
          | split;
            [ exact Hrefined
            | transitivity (phase1_surface_field_list_spine_tree base);
              [ eapply phase1_surface_normalize_field_type_list_spine_round_trip;
                exact Hrefined
              | eapply phase1_surface_normalize_field_list_spine_round_trip;
                exact Hbase ] ] ] ] ]
  end.
Qed.
