From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSourceHeader
  GrammarAstSourceHeaderTotality
  GrammarAstRecordFieldsSpine
  GrammarAstFieldTypeSpine
  GrammarAstFieldTypeListSpine
  GrammarAstFieldTypeTotality
  GrammarAstRecordFieldsTotality.

Import ListNotations.
Open Scope string_scope.

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
      [ ELiteral ","; ENonterminal "field_decl" ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ELiteral ",") [ENonterminal "field_decl"]
      input rest trees Hitems)
    as [after_comma [comma_tree [tail_trees
      [Htrees [Hcomma Htail]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ENonterminal "field_decl") []
      after_comma rest tail_trees Htail)
    as [after_field [field_tree [nil_trees
      [Htail_trees [Hfield Hnil]]]]].
  rewrite Htrees, Htail_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "," _ _ comma_tree Hcomma)
    as [comma_tail [_ [_ Hcomma_tree]]].
  destruct
    (phase1_surface_normalize_field_type_layers_total_from_derivation
      _ _ _ field_tree Hfield)
    as [base [refined [Hbase [Hrefined Hrefined_tree]]]].
  assert (Hsuffix :
    phase1_surface_normalize_field_suffix tree = Some base).
  {
    rewrite Htree, Hcomma_tree.
    unfold phase1_surface_normalize_field_suffix,
      phase1_surface_expect_sequence,
      phase1_surface_exact2,
      phase1_surface_expect_literal.
    cbn.
    rewrite Hbase.
    reflexivity.
  }
  exists base, refined.
  split.
  - exact Hsuffix.
  - split.
    + exact Hrefined.
    + unfold phase1_surface_field_type_suffix_tree.
      rewrite Htree, Hcomma_tree, Hrefined_tree.
      reflexivity.
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
        EOptional (ELiteral ",") ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 0
      (ENonterminal "field_decl")
      [ ERepetition phase1_surface_field_suffix_expression_for_totality;
        EOptional (ELiteral ",") ]
      input rest trees Hitems)
    as [after_first [first_tree [tail1_trees
      [Htrees [Hfirst Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 1
      (ERepetition phase1_surface_field_suffix_expression_for_totality)
      [ EOptional (ELiteral ",") ]
      after_first rest tail1_trees Htail1)
    as [after_rest [rest_tree [tail2_trees
      [Htail1_trees [Hrest Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules path 2
      (EOptional (ELiteral ",")) []
      after_rest rest tail2_trees Htail2)
    as [after_trailing [trailing_tree [nil_trees
      [Htail2_trees [Htrailing Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Htree.
  inversion Hnil; subst nil_trees.
  destruct
    (phase1_surface_normalize_field_type_layers_total_from_derivation
      _ _ _ first_tree Hfirst)
    as [base_first [refined_first
        [Hbase_first [Hrefined_first Hrefined_first_tree]]]].
  destruct
    (phase1_surface_repetition_derivation_exposes
      _ phase1_surface_field_suffix_expression_for_totality
      _ _ rest_tree Hrest)
    as [rest_trees [Hrest_tree Hrest_body]].
  destruct
    (phase1_surface_normalize_field_type_suffixes_layers_total_from_repetition
      _ phase1_surface_field_suffix_expression_for_totality
      _ _ rest_trees Hrest_body eq_refl)
    as [base_rest [refined_rest [Hbase_rest Hrefined_rest]]].
  destruct
    (phase1_surface_normalize_trailing_comma_total_from_derivation
      _ _ _ trailing_tree Htrailing)
    as [trailing [Htrailing_normalize Htrailing_round_trip]].
  pose (base :=
    {| phase1_field_list_spine_first := base_first;
       phase1_field_list_spine_rest := base_rest;
       phase1_field_list_spine_trailing_comma := trailing |}).
  pose (refined :=
    {| phase1_field_type_list_spine_first := refined_first;
       phase1_field_type_list_spine_rest := refined_rest;
       phase1_field_type_list_spine_trailing_comma := trailing |}).
  assert (Hbase :
    phase1_surface_normalize_field_list_spine tree = Some base).
  {
    rewrite Htree, Hrest_tree.
    unfold phase1_surface_normalize_field_list_spine,
      phase1_surface_expect_sequence,
      phase1_surface_exact3,
      phase1_surface_expect_repetition.
    cbn.
    rewrite Hbase_first, Htrailing_normalize, Hbase_rest.
    reflexivity.
  }
  assert (Hrefined :
    phase1_surface_normalize_field_type_list_spine base = Some refined).
  {
    unfold phase1_surface_normalize_field_type_list_spine, base.
    cbn.
    rewrite Hrefined_first, Hrefined_rest.
    reflexivity.
  }
  exists base, refined.
  split.
  - exact Hbase.
  - split.
    + exact Hrefined.
    + transitivity (phase1_surface_field_list_spine_tree base).
      * eapply phase1_surface_normalize_field_type_list_spine_round_trip.
        exact Hrefined.
      * eapply phase1_surface_normalize_field_list_spine_round_trip.
        exact Hbase.
Qed.
