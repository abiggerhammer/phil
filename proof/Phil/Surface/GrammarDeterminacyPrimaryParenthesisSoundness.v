From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyStructuralScannerSoundness
  GrammarDeterminacyParenthesisNeutralSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic soundness for the parenthesis-led primary_expression overlap.

  Both tuple_expression and parenthesized_expression begin with "(" followed
  by an ordinary expression derivation.  The parenthesis-neutral foundation
  proves that the consumed expression prefix preserves depth zero, so the next
  comma/close token forces the structural resolver decision.
*)

Lemma derives_sequence_open_expression_separator_prefix :
  forall path separator tail_items input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        (ELiteral "(" ::
         ENonterminal "expression" ::
         ELiteral separator ::
         tail_items))
      input rest tree ->
    exists consumed suffix,
      input =
        TLiteral "(" ::
        (consumed ++ TLiteral separator :: suffix) /\
      parenthesis_neutral_scan 0 consumed = Some 0.
Proof.
  intros path separator tail_items input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      (ELiteral "(" ::
       ENonterminal "expression" ::
       ELiteral separator ::
       tail_items)
      input rest tree Hderive)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 0
      (ELiteral "(")
      (ENonterminal "expression" :: ELiteral separator :: tail_items)
      input rest trees Hitems)
    as [after_open [open_tree [tail_trees [Hopen Htail]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 0))
      "(" input after_open open_tree Hopen)
    as [open_tail [Hinput [Hafter_open _]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 1
      (ENonterminal "expression")
      (ELiteral separator :: tail_items)
      after_open rest tail_trees Htail)
    as [after_expression
        [expression_tree [remaining_trees [Hexpression Hremaining]]]].
  destruct
    (phase1_surface_expression_derivation_is_parenthesis_neutral
      (descend path (AtSequence 1))
      after_open after_expression expression_tree Hexpression)
    as [consumed [Hexpression_input Hneutral]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 2
      (ELiteral separator) tail_items
      after_expression rest remaining_trees Hremaining)
    as [after_separator
        [separator_tree [separator_tail_trees [Hseparator _]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 2))
      separator after_expression after_separator separator_tree Hseparator)
    as [suffix [Hseparator_input [_ _]]].
  exists consumed, suffix.
  split.
  - rewrite Hinput.
    rewrite <- Hafter_open.
    rewrite Hexpression_input.
    rewrite Hseparator_input.
    reflexivity.
  - exact Hneutral.
Qed.

Lemma phase1_surface_tuple_expression_lookup_prefix :
  exists tail_items,
    lookupRule "tuple_expression" phase1_surface_rules =
      Some
        (ESequence
          (ELiteral "(" ::
           ENonterminal "expression" ::
           ELiteral "," ::
           tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Lemma phase1_surface_parenthesized_expression_lookup_prefix :
  exists tail_items,
    lookupRule "parenthesized_expression" phase1_surface_rules =
      Some
        (ESequence
          (ELiteral "(" ::
           ENonterminal "expression" ::
           ELiteral ")" ::
           tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Theorem phase1_surface_tuple_expression_derivation_commits_primary_tuple_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "tuple_expression") input rest tree ->
    primary_expression_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_tuple_expression_lookup_prefix
    as [tail_items Hlookup_exact].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "tuple_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hlookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_open_expression_separator_prefix
      (descend path (AtNonterminal "tuple_expression"))
      "," tail_items input rest subtree Hbody)
    as [consumed [suffix [Hinput Hneutral]]].
  rewrite Hinput.
  apply primary_expression_neutral_comma_commits_tuple.
  exact Hneutral.
Qed.

Theorem phase1_surface_parenthesized_expression_derivation_commits_primary_grouping_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "parenthesized_expression") input rest tree ->
    primary_expression_decision input = Some (ChooseAlternative 1).
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_parenthesized_expression_lookup_prefix
    as [tail_items Hlookup_exact].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "parenthesized_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hlookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_open_expression_separator_prefix
      (descend path (AtNonterminal "parenthesized_expression"))
      ")" tail_items input rest subtree Hbody)
    as [consumed [suffix [Hinput Hneutral]]].
  rewrite Hinput.
  apply primary_expression_neutral_close_commits_grouping.
  exact Hneutral.
Qed.

Theorem phase1_surface_primary_parenthesis_structural_overlap_semantic_sound :
  (forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "tuple_expression") input rest tree ->
    primary_expression_decision input = Some (ChooseAlternative 0)) /\
  (forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "parenthesized_expression") input rest tree ->
    primary_expression_decision input = Some (ChooseAlternative 1)).
Proof.
  split.
  - exact phase1_surface_tuple_expression_derivation_commits_primary_tuple_branch.
  - exact phase1_surface_parenthesized_expression_derivation_commits_primary_grouping_branch.
Qed.
