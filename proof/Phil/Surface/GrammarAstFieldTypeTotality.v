From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstSourceHeader
  GrammarAstFieldTypeSpine
  GrammarAstRecordFieldsSpine
  GrammarAstGenericRequirementsTotality
  GrammarAstRecordFieldsTotality
  GrammarAstStaticTypeArgumentCarrierTotality
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the field type-expression payload refinement from #1161. *)

Theorem phase1_surface_normalize_field_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "field_decl")
      input rest tree ->
    exists field,
      phase1_surface_normalize_field_type_tree tree = Some field /\
      phase1_surface_field_type_spine_tree field = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "field_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_field_decl_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "field_decl"))
      [ ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "field_decl")) 0
      (ENonterminal "identifier")
      [ ELiteral ":";
        ENonterminal "type_expression" ]
      input rest trees Hitems)
    as [after_name [name_tree [tail1_trees
      [Htrees [Hname Htail1]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "field_decl")) 1
      (ELiteral ":")
      [ ENonterminal "type_expression" ]
      after_name rest tail1_trees Htail1)
    as [after_colon [colon_tree [tail2_trees
      [Htail1_trees [Hcolon Htail2]]]]].
  destruct
    (derives_sequence_cons_exposes_head_exact
      phase1_surface_rules
      (descend path (AtNonterminal "field_decl")) 2
      (ENonterminal "type_expression") []
      after_colon rest tail2_trees Htail2)
    as [after_type [type_tree [nil_trees
      [Htail2_trees [Htype Hnil]]]]].
  rewrite Htrees, Htail1_trees, Htail2_trees in Hsubtree.
  inversion Hnil; subst nil_trees.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules _ ":" _ _ colon_tree Hcolon)
    as [colon_tail [_ [_ Hcolon_tree]]].
  destruct
    (phase1_surface_normalize_identifier_total_from_derivation
      _ _ _ name_tree Hname)
    as [name Hname_normalize].
  pose proof
    (phase1_surface_validate_named_node_total_from_derivation
      "type_expression" _ _ _ type_tree Htype) as Htype_validate.
  destruct
    (phase1_surface_normalize_static_type_arguments_type_tree_total_from_derivation
      _ _ _ type_tree Htype)
    as [type_value [Htype_normalize Htype_round_trip]].
  pose (base :=
    {| phase1_field_spine_name := name;
       phase1_field_spine_type_tree := type_tree |}).
  pose (refined :=
    {| phase1_field_type_spine_name := name;
       phase1_field_type_spine_type := type_value |}).
  assert (Hbase :
    phase1_surface_normalize_field_spine tree = Some base).
  {
    rewrite Htree, Hsubtree, Hcolon_tree.
    unfold phase1_surface_normalize_field_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_sequence,
      phase1_surface_exact3,
      phase1_surface_expect_literal.
    cbn.
    repeat rewrite String.eqb_refl.
    rewrite Hname_normalize.
    rewrite Htype_validate.
    unfold base.
    reflexivity.
  }
  assert (Hrefined :
    phase1_surface_normalize_field_type_spine base = Some refined).
  {
    unfold phase1_surface_normalize_field_type_spine, base.
    cbn.
    rewrite Htype_normalize.
    unfold refined.
    reflexivity.
  }
  assert (Hnormalize :
    phase1_surface_normalize_field_type_tree tree = Some refined).
  {
    unfold phase1_surface_normalize_field_type_tree.
    rewrite Hbase.
    exact Hrefined.
  }
  exists refined.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_field_type_tree_round_trip.
    exact Hnormalize.
Qed.
