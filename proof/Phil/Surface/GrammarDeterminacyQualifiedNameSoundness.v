From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyStructuralScannerSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic bridge for the qualified-name structural overlap.

  The pattern resolver commits record-pattern syntax after the maximal
  qualified-name scanner reaches a following left brace.  The scanner tranche
  already proves that token-level fact.  This file connects it to arbitrary
  ordinary Grammar-v1 derivations by proving that qualified_name consumes
  exactly IDENTIFIER followed by zero or more "." IDENTIFIER pairs, then
  exposing the opening brace of record_pattern.
*)

Lemma derives_sequence_nil_input_eq_rest :
  forall rules path index input rest trees,
    DerivesSequence rules path index [] input rest trees ->
    input = rest.
Proof.
  intros rules path index input rest trees Hderive.
  inversion Hderive.
  reflexivity.
Qed.

Lemma derives_repetition_expression_exposes_body :
  forall rules path body input rest tree,
    Derives rules path (ERepetition body) input rest tree ->
    exists trees,
      tree = PTRepetition trees /\
      DerivesRepetition rules path body input rest trees.
Proof.
  intros rules path body input rest tree Hderive.
  inversion Hderive; subst.
  eexists.
  split; eauto.
Qed.

Lemma phase1_surface_qualified_name_lookup_exact :
  lookupRule "qualified_name" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "identifier"
        ; ERepetition
            (ESequence
              [ELiteral "."; ENonterminal "identifier"])
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_dot_identifier_derivation_is_exact :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence [ELiteral "."; ENonterminal "identifier"])
      input rest tree ->
    exists lexeme,
      input =
        TLiteral "." :: TLexical "IDENTIFIER" lexeme :: rest.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ELiteral "."; ENonterminal "identifier"]
      input rest tree Hderive)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 0
      (ELiteral ".") [ENonterminal "identifier"]
      input rest trees Hitems)
    as [middle [literal_tree [tail_trees [Hliteral Htail]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 0))
      "." input middle literal_tree Hliteral)
    as [after_literal [Hinput [Hmiddle _]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 1
      (ENonterminal "identifier") []
      middle rest tail_trees Htail)
    as [after_identifier
        [identifier_tree [nil_trees [Hidentifier Hnil]]]].
  destruct
    (phase1_surface_identifier_derivation_is_exact
      (descend path (AtSequence 1))
      middle after_identifier identifier_tree Hidentifier)
    as [lexeme
        [identifier_tail [Hidentifier_input Hidentifier_rest]]].
  pose proof
    (derives_sequence_nil_input_eq_rest
      phase1_surface_rules path 2
      after_identifier rest nil_trees Hnil)
    as Hnil_rest.
  exists lexeme.
  rewrite Hinput.
  rewrite <- Hmiddle.
  rewrite Hidentifier_input.
  rewrite <- Hidentifier_rest.
  rewrite Hnil_rest.
  reflexivity.
Qed.

Lemma phase1_surface_qualified_name_repetition_body_is_exact :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ESequence [ELiteral "."; ENonterminal "identifier"] ->
    exists names,
      input = qualified_name_dot_tokens names rest.
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
      (phase1_surface_dot_identifier_derivation_is_exact
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [name Hinput].
    destruct (IHrest eq_refl) as [names Hmiddle].
    exists (name :: names).
    simpl.
    rewrite Hinput.
    rewrite Hmiddle.
    reflexivity.
Qed.

Lemma phase1_surface_qualified_name_repetition_is_exact :
  forall path input rest trees,
    DerivesRepetition phase1_surface_rules path
      (ESequence [ELiteral "."; ENonterminal "identifier"])
      input rest trees ->
    exists names,
      input = qualified_name_dot_tokens names rest.
Proof.
  intros path input rest trees Hderive.
  eapply phase1_surface_qualified_name_repetition_body_is_exact.
  - exact Hderive.
  - reflexivity.
Qed.

Theorem phase1_surface_qualified_name_derivation_is_exact :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "qualified_name") input rest tree ->
    exists first_name more_names,
      input =
        TLexical "IDENTIFIER" first_name ::
        qualified_name_dot_tokens more_names rest.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "qualified_name"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_qualified_name_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "qualified_name"))
      [ ENonterminal "identifier"
      ; ERepetition
          (ESequence [ELiteral "."; ENonterminal "identifier"])
      ]
      input rest subtree Hbody)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "qualified_name")) 0
      (ENonterminal "identifier")
      [ ERepetition
          (ESequence [ELiteral "."; ENonterminal "identifier"])
      ]
      input rest trees Hitems)
    as [after_identifier
        [identifier_tree [tail_trees [Hidentifier Htail]]]].
  destruct
    (phase1_surface_identifier_derivation_is_exact
      (descend
        (descend path (AtNonterminal "qualified_name"))
        (AtSequence 0))
      input after_identifier identifier_tree Hidentifier)
    as [first_name
        [identifier_tail [Hinput Hidentifier_rest]]].
  assert (Hinput_prefix :
    input = TLexical "IDENTIFIER" first_name :: after_identifier).
  {
    rewrite Hinput.
    rewrite <- Hidentifier_rest.
    reflexivity.
  }
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "qualified_name")) 1
      (ERepetition
        (ESequence [ELiteral "."; ENonterminal "identifier"]))
      []
      after_identifier rest tail_trees Htail)
    as [after_repetition
        [repetition_tree [nil_trees [Hrepetition Hnil]]]].
  destruct
    (derives_repetition_expression_exposes_body
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "qualified_name"))
        (AtSequence 1))
      (ESequence [ELiteral "."; ENonterminal "identifier"])
      after_identifier after_repetition repetition_tree Hrepetition)
    as [repetition_trees [_ Hrepetition_body]].
  destruct
    (phase1_surface_qualified_name_repetition_is_exact
      (descend
        (descend path (AtNonterminal "qualified_name"))
        (AtSequence 1))
      after_identifier after_repetition repetition_trees Hrepetition_body)
    as [more_names Hmore].
  pose proof
    (derives_sequence_nil_input_eq_rest
      phase1_surface_rules
      (descend path (AtNonterminal "qualified_name")) 2
      after_repetition rest nil_trees Hnil)
    as Hnil_rest.
  exists first_name, more_names.
  rewrite Hinput_prefix.
  rewrite Hmore.
  rewrite Hnil_rest.
  reflexivity.
Qed.

Lemma phase1_surface_record_pattern_lookup_prefix :
  exists tail_items,
    lookupRule "record_pattern" phase1_surface_rules =
      Some
        (ESequence
          (ENonterminal "qualified_name" ::
           ELiteral "{" ::
           tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Theorem phase1_surface_record_pattern_derivation_commits_pattern_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "record_pattern") input rest tree ->
    pattern_decision input = Some (ChooseAlternative 2).
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_record_pattern_lookup_prefix
    as [tail_items Hlookup_exact].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "record_pattern"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hlookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "record_pattern"))
      (ENonterminal "qualified_name" :: ELiteral "{" :: tail_items)
      input rest subtree Hbody)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "record_pattern")) 0
      (ENonterminal "qualified_name")
      (ELiteral "{" :: tail_items)
      input rest trees Hitems)
    as [after_name
        [name_tree [tail_trees [Hname Htail]]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "record_pattern")) 1
      (ELiteral "{") tail_items
      after_name rest tail_trees Htail)
    as [after_open [open_tree [remaining_trees [Hopen _]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "record_pattern"))
        (AtSequence 1))
      "{" after_name after_open open_tree Hopen)
    as [open_tail [Hafter_name [_ _]]].
  destruct
    (phase1_surface_qualified_name_derivation_is_exact
      (descend
        (descend path (AtNonterminal "record_pattern"))
        (AtSequence 0))
      input after_name name_tree Hname)
    as [first_name [more_names Hinput]].
  rewrite Hinput.
  rewrite Hafter_name.
  apply pattern_decision_qualified_name_brace_tail.
Qed.
