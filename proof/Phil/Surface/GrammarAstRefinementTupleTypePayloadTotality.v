From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
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
    Hbinder : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?binder_tree,
    Hcolon : Derives phase1_surface_rules _
      (ELiteral ":") _ _ ?colon_tree,
    Hbase : Derives phase1_surface_rules _
      (ENonterminal "type_expression") _ _ ?base_type_tree,
    Hbar : Derives phase1_surface_rules _
      (ELiteral "|") _ _ ?bar_tree,
    Hproposition : Derives phase1_surface_rules _
      (ENonterminal "proposition") _ _ ?proposition_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "}") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "{" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ":" _ _ colon_tree Hcolon)
        as [colon_tail [_ [_ Hcolon_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "|" _ _ bar_tree Hbar)
        as [bar_tail [_ [_ Hbar_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "}" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (phase1_surface_normalize_identifier_total_from_derivation
          _ _ _ binder_tree Hbinder)
        as [binder Hbinder_normalize];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "type_expression" _ _ _ base_type_tree Hbase)
        as Hbase_validate;
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "proposition" _ _ _ proposition_tree Hproposition)
        as Hproposition_validate;
      let refinement := constr:(
        {| phase1_refinement_type_spine_binder := binder;
           phase1_refinement_type_spine_base_type_tree := base_type_tree;
           phase1_refinement_type_spine_proposition_tree := proposition_tree |}) in
      assert (Hnormalize :
        phase1_surface_normalize_refinement_type_spine tree = Some refinement);
      [ rewrite Htree, Hsubtree_tree, Hopen_tree, Hcolon_tree,
          Hbar_tree, Hclose_tree;
        unfold phase1_surface_normalize_refinement_type_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact7,
          phase1_surface_expect_literal;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Hbinder_normalize;
        rewrite Hbase_validate;
        rewrite Hproposition_validate;
        reflexivity
      | exists refinement;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_refinement_type_spine_round_trip;
          exact Hnormalize ] ]
  end.
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
    Hfirst : Derives phase1_surface_rules _
      (ENonterminal "type_expression") _ _ ?first_tree,
    Hcomma : Derives phase1_surface_rules _
      (ELiteral ",") _ _ ?comma_tree,
    Hsecond : Derives phase1_surface_rules _
      (ENonterminal "type_expression") _ _ ?second_tree,
    Hrest : Derives phase1_surface_rules _
      (ERepetition phase1_surface_tuple_type_suffix_expression_for_totality)
      _ _ ?rest_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral ")") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "(" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "," _ _ comma_tree Hcomma)
        as [comma_tail [_ [_ Hcomma_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ")" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "type_expression" _ _ _ first_tree Hfirst)
        as Hfirst_validate;
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "type_expression" _ _ _ second_tree Hsecond)
        as Hsecond_validate;
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
      let tuple_type := constr:(
        {| phase1_tuple_type_spine_first := first_tree;
           phase1_tuple_type_spine_second := second_tree;
           phase1_tuple_type_spine_rest := rest_types |}) in
      assert (Hnormalize :
        phase1_surface_normalize_tuple_type_spine tree = Some tuple_type);
      [ rewrite Htree, Hsubtree_tree, Hopen_tree, Hcomma_tree,
          Hrest_tree, Hclose_tree;
        unfold phase1_surface_normalize_tuple_type_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact6,
          phase1_surface_expect_literal,
          phase1_surface_expect_repetition;
        cbn;
        repeat rewrite String.eqb_refl;
        rewrite Hfirst_validate;
        rewrite Hsecond_validate;
        rewrite Hrest_normalize;
        reflexivity
      | exists tuple_type;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_tuple_type_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.
