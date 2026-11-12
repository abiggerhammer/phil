From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSourceHeaderTotality
  GrammarAstGenericRequirementsTotality
  GrammarAstRefinementTupleTypePayloadSpine
  GrammarAstShallowCompoundTypePayloadTotality
  GrammarAstDataTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the final two nonreference type shells introduced by #974. *)

Definition phase1_surface_refinement_type_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "{";
      ENonterminal "identifier";
      ELiteral ":";
      ENonterminal "type_expression";
      ELiteral "|";
      ENonterminal "proposition";
      ELiteral "}"
    ].

Definition phase1_surface_tuple_type_expression_for_totality
  : EbnfExpression :=
  ESequence
    [ ELiteral "(";
      ENonterminal "type_expression";
      ELiteral ",";
      ENonterminal "type_expression";
      ERepetition phase1_surface_tuple_type_suffix_expression_for_totality;
      ELiteral ")"
    ].

Lemma phase1_surface_refinement_type_lookup_for_totality :
  lookupRule "refinement_type" phase1_surface_rules =
    Some phase1_surface_refinement_type_expression_for_totality.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_tuple_type_lookup_for_totality :
  lookupRule "tuple_type" phase1_surface_rules =
    Some phase1_surface_tuple_type_expression_for_totality.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_normalize_refinement_type_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "refinement_type")
      input rest tree ->
    exists refinement,
      phase1_surface_normalize_refinement_type_spine tree = Some refinement /\
      phase1_surface_refinement_type_spine_tree refinement = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "refinement_type"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_refinement_type_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  unfold phase1_surface_refinement_type_expression_for_totality in Hbody.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "refinement_type"))
      [ ELiteral "{";
        ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression";
        ELiteral "|";
        ENonterminal "proposition";
        ELiteral "}"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree_tree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 0 (ELiteral "{") [ENonterminal "identifier"; ELiteral ":"; ENonterminal "type_expression"; ELiteral "|"; ENonterminal "proposition"; ELiteral "}"]
      input rest trees Hitems)
    as [after_open [open_tree [tail1_trees
      [Htrees [Hopen Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 1 (ENonterminal "identifier") [ELiteral ":"; ENonterminal "type_expression"; ELiteral "|"; ENonterminal "proposition"; ELiteral "}"]
      after_open rest tail1_trees Htail1)
    as [after_binder [binder_tree [tail2_trees
      [Htail1_trees [Hbinder Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 2 (ELiteral ":") [ENonterminal "type_expression"; ELiteral "|"; ENonterminal "proposition"; ELiteral "}"]
      after_binder rest tail2_trees Htail2)
    as [after_colon [colon_tree [tail3_trees
      [Htail2_trees [Hcolon Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 3 (ENonterminal "type_expression") [ELiteral "|"; ENonterminal "proposition"; ELiteral "}"]
      after_colon rest tail3_trees Htail3)
    as [after_base [base_tree [tail4_trees
      [Htail3_trees [Hbase Htail4]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 4 (ELiteral "|") [ENonterminal "proposition"; ELiteral "}"]
      after_base rest tail4_trees Htail4)
    as [after_bar [bar_tree [tail5_trees
      [Htail4_trees [Hbar Htail5]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 5 (ENonterminal "proposition") [ELiteral "}"]
      after_bar rest tail5_trees Htail5)
    as [after_proposition [proposition_tree [tail6_trees
      [Htail5_trees [Hproposition Htail6]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 6 (ELiteral "}") []
      after_proposition rest tail6_trees Htail6)
    as [after_close [close_tree [nil_trees
      [Htail6_trees [Hclose Htail7]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees, Htail4_trees, Htail5_trees, Htail6_trees in Hsubtree_tree.
  inversion Htail7; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "{" _ _ open_tree Hopen)
    as [open_tail [_ [_ Hopen_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ":" _ _ colon_tree Hcolon)
    as [colon_tail [_ [_ Hcolon_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "|" _ _ bar_tree Hbar)
    as [bar_tail [_ [_ Hbar_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "}" _ _ close_tree Hclose)
    as [close_tail [_ [_ Hclose_tree]]].
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ binder_tree Hbinder)
    as [binder Hbinder_normalize].
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "type_expression" _ _ _ base_tree Hbase)
    as Hbase_validate.
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "proposition" _ _ _ proposition_tree Hproposition)
    as Hproposition_validate.
  pose (refinement :=
    {| phase1_refinement_type_spine_binder := binder;
       phase1_refinement_type_spine_base_type_tree := base_tree;
       phase1_refinement_type_spine_proposition_tree := proposition_tree |}).
  assert (Hnormalize :
    phase1_surface_normalize_refinement_type_spine tree = Some refinement).
  {
    rewrite Htree, Hsubtree_tree, Hopen_tree, Hcolon_tree,
      Hbar_tree, Hclose_tree.
    unfold phase1_surface_normalize_refinement_type_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact7,
      phase1_surface_expect_literal.
    cbn.
    repeat rewrite String.eqb_refl.
    rewrite Hbinder_normalize.
    rewrite Hbase_validate.
    rewrite Hproposition_validate.
    reflexivity.
  }
  exists refinement.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_refinement_type_spine_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_tuple_type_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "tuple_type")
      input rest tree ->
    exists tuple_type,
      phase1_surface_normalize_tuple_type_spine tree = Some tuple_type /\
      phase1_surface_tuple_type_spine_tree tuple_type = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "tuple_type"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_tuple_type_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  unfold phase1_surface_tuple_type_expression_for_totality in Hbody.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "tuple_type"))
      [ ELiteral "(";
        ENonterminal "type_expression";
        ELiteral ",";
        ENonterminal "type_expression";
        ERepetition phase1_surface_tuple_type_suffix_expression_for_totality;
        ELiteral ")"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree_tree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 0 (ELiteral "(") [ENonterminal "type_expression"; ELiteral ","; ENonterminal "type_expression"; ERepetition phase1_surface_tuple_type_suffix_expression_for_totality; ELiteral ")"]
      input rest trees Hitems)
    as [after_open [open_tree [tail1_trees
      [Htrees [Hopen Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 1 (ENonterminal "type_expression") [ELiteral ","; ENonterminal "type_expression"; ERepetition phase1_surface_tuple_type_suffix_expression_for_totality; ELiteral ")"]
      after_open rest tail1_trees Htail1)
    as [after_first [first_tree [tail2_trees
      [Htail1_trees [Hfirst Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 2 (ELiteral ",") [ENonterminal "type_expression"; ERepetition phase1_surface_tuple_type_suffix_expression_for_totality; ELiteral ")"]
      after_first rest tail2_trees Htail2)
    as [after_comma [comma_tree [tail3_trees
      [Htail2_trees [Hcomma Htail3]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 3 (ENonterminal "type_expression") [ERepetition phase1_surface_tuple_type_suffix_expression_for_totality; ELiteral ")"]
      after_comma rest tail3_trees Htail3)
    as [after_second [second_tree [tail4_trees
      [Htail3_trees [Hsecond Htail4]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 4 (ERepetition phase1_surface_tuple_type_suffix_expression_for_totality) [ELiteral ")"]
      after_second rest tail4_trees Htail4)
    as [after_rest [rest_tree [tail5_trees
      [Htail4_trees [Hrest Htail5]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules _ 5 (ELiteral ")") []
      after_rest rest tail5_trees Htail5)
    as [after_close [close_tree [nil_trees
      [Htail5_trees [Hclose Htail6]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees, Htail3_trees, Htail4_trees, Htail5_trees in Hsubtree_tree.
  inversion Htail6; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "(" _ _ open_tree Hopen)
    as [open_tail [_ [_ Hopen_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ "," _ _ comma_tree Hcomma)
    as [comma_tail [_ [_ Hcomma_tree]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ")" _ _ close_tree Hclose)
    as [close_tail [_ [_ Hclose_tree]]].
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "type_expression" _ _ _ first_tree Hfirst)
    as Hfirst_validate.
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "type_expression" _ _ _ second_tree Hsecond)
    as Hsecond_validate.
  destruct
    (phase1_surface_repetition_derivation_exposes
      _ phase1_surface_tuple_type_suffix_expression_for_totality
      _ _ rest_tree Hrest)
    as [rest_trees [Hrest_tree Hrest_body]].
  destruct
    (phase1_surface_normalize_tuple_type_suffixes_total_from_repetition
      _ phase1_surface_tuple_type_suffix_expression_for_totality
      _ _ rest_trees Hrest_body eq_refl)
    as [rest_types Hrest_normalize].
  pose (tuple_type :=
    {| phase1_tuple_type_spine_first := first_tree;
       phase1_tuple_type_spine_second := second_tree;
       phase1_tuple_type_spine_rest := rest_types |}).
  assert (Hnormalize :
    phase1_surface_normalize_tuple_type_spine tree = Some tuple_type).
  {
    rewrite Htree, Hsubtree_tree, Hopen_tree, Hcomma_tree,
      Hrest_tree, Hclose_tree.
    unfold phase1_surface_normalize_tuple_type_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact6,
      phase1_surface_expect_literal,
      phase1_surface_expect_repetition.
    cbn.
    repeat rewrite String.eqb_refl.
    rewrite Hfirst_validate.
    rewrite Hsecond_validate.
    rewrite Hrest_normalize.
    reflexivity.
  }
  exists tuple_type.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_tuple_type_spine_round_trip.
    exact Hnormalize.
Qed.
