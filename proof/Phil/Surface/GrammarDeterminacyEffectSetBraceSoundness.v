From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyStructuralScannerSoundness
  GrammarDeterminacyQualifiedNameSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic soundness for the effect-set side of the brace-led
  static_argument overlap.

  The structural resolver commits branch 3 for an empty brace pair and for a
  nonempty brace whose first identifier is not immediately followed by ":".
  This file connects those token-level scanner facts to arbitrary ordinary
  Grammar-v1 derivations of effect_set_literal.
*)

Lemma derives_optional_input_cases :
  forall rules path body input rest tree,
    Derives rules path (EOptional body) input rest tree ->
    input = rest \/
    exists subtree,
      Derives rules (descend path AtOptionalBody)
        body input rest subtree.
Proof.
  intros rules path body input rest tree Hderive.
  inversion Hderive; subst.
  - left.
    reflexivity.
  - right.
    eexists.
    eauto.
Qed.

Lemma derives_repetition_input_cases :
  forall rules path body input rest trees,
    DerivesRepetition rules path body input rest trees ->
    input = rest \/
    exists middle tree tail_trees,
      Derives rules (descend path AtRepetitionBody)
        body input middle tree /\
      DerivesRepetition rules path body middle rest tail_trees.
Proof.
  intros rules path body input rest trees Hderive.
  inversion Hderive; subst.
  - left.
    reflexivity.
  - right.
    do 3 eexists.
    split; eauto.
Qed.

Lemma phase1_surface_sequence_literal_prefix :
  forall path literal tail_items input rest tree,
    Derives phase1_surface_rules path
      (ESequence (ELiteral literal :: tail_items))
      input rest tree ->
    exists suffix,
      input = TLiteral literal :: suffix.
Proof.
  intros path literal tail_items input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      (ELiteral literal :: tail_items)
      input rest tree Hderive)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 0
      (ELiteral literal) tail_items
      input rest trees Hitems)
    as [middle [literal_tree [tail_trees [Hliteral _]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 0))
      literal input middle literal_tree Hliteral)
    as [suffix [Hinput [_ _]]].
  exists suffix.
  exact Hinput.
Qed.

Lemma phase1_surface_nonterminal_sequence_literal_prefix :
  forall name literal tail_items path input rest tree,
    lookupRule name phase1_surface_rules =
      Some (ESequence (ELiteral literal :: tail_items)) ->
    Derives phase1_surface_rules path
      (ENonterminal name) input rest tree ->
    exists suffix,
      input = TLiteral literal :: suffix.
Proof.
  intros name literal tail_items path input rest tree Hlookup_exact Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path name input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hlookup_exact in Hlookup.
  inversion Hlookup; subst body.
  eapply phase1_surface_sequence_literal_prefix.
  exact Hbody.
Qed.

Lemma phase1_surface_static_arguments_lookup_prefix :
  exists tail_items,
    lookupRule "static_arguments" phase1_surface_rules =
      Some (ESequence (ELiteral "[" :: tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Lemma phase1_surface_term_arguments_lookup_prefix :
  exists tail_items,
    lookupRule "term_arguments" phase1_surface_rules =
      Some (ESequence (ELiteral "(" :: tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Lemma phase1_surface_static_arguments_derivation_starts_open_bracket :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "static_arguments") input rest tree ->
    exists suffix,
      input = TLiteral "[" :: suffix.
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_static_arguments_lookup_prefix
    as [tail_items Hlookup].
  eapply phase1_surface_nonterminal_sequence_literal_prefix.
  - exact Hlookup.
  - exact Hderive.
Qed.

Lemma phase1_surface_term_arguments_derivation_starts_open_parenthesis :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "term_arguments") input rest tree ->
    exists suffix,
      input = TLiteral "(" :: suffix.
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_term_arguments_lookup_prefix
    as [tail_items Hlookup].
  eapply phase1_surface_nonterminal_sequence_literal_prefix.
  - exact Hlookup.
  - exact Hderive.
Qed.

Lemma phase1_surface_static_reference_lookup_exact :
  lookupRule "static_reference" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "qualified_name"
        ; EOptional (ENonterminal "static_arguments")
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_effect_expression_lookup_exact :
  lookupRule "effect_expression" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "static_reference"
        ; EOptional (ENonterminal "term_arguments")
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_effect_expression_identifier_tail_classification :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "effect_expression") input rest tree ->
    exists first_name tail,
      input = TLexical "IDENTIFIER" first_name :: tail /\
      ((exists suffix, tail = TLiteral "." :: suffix) \/
       (exists suffix, tail = TLiteral "[" :: suffix) \/
       (exists suffix, tail = TLiteral "(" :: suffix) \/
       tail = rest).
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_expression"
      input rest tree Hderive)
    as [effect_body [effect_tree [Heffect_lookup [_ Heffect_body]]]].
  rewrite phase1_surface_effect_expression_lookup_exact in Heffect_lookup.
  inversion Heffect_lookup; subst effect_body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "effect_expression"))
      [ ENonterminal "static_reference"
      ; EOptional (ENonterminal "term_arguments")
      ]
      input rest effect_tree Heffect_body)
    as [effect_trees [_ Heffect_items]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "effect_expression")) 0
      (ENonterminal "static_reference")
      [EOptional (ENonterminal "term_arguments")]
      input rest effect_trees Heffect_items)
    as [after_static_reference
        [static_reference_tree
          [effect_tail_trees [Hstatic_reference Heffect_tail]]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "effect_expression")) 1
      (EOptional (ENonterminal "term_arguments")) []
      after_static_reference rest effect_tail_trees Heffect_tail)
    as [after_term_arguments
        [term_arguments_tree [effect_nil_trees [Hterm_arguments Heffect_nil]]]].
  pose proof
    (derives_sequence_nil_input_eq_rest
      phase1_surface_rules
      (descend path (AtNonterminal "effect_expression")) 2
      after_term_arguments rest effect_nil_trees Heffect_nil)
    as Hafter_term_arguments.

  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "effect_expression"))
        (AtSequence 0))
      "static_reference"
      input after_static_reference static_reference_tree Hstatic_reference)
    as [static_body [static_tree [Hstatic_lookup [_ Hstatic_body]]]].
  rewrite phase1_surface_static_reference_lookup_exact in Hstatic_lookup.
  inversion Hstatic_lookup; subst static_body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend
        (descend
          (descend path (AtNonterminal "effect_expression"))
          (AtSequence 0))
        (AtNonterminal "static_reference"))
      [ ENonterminal "qualified_name"
      ; EOptional (ENonterminal "static_arguments")
      ]
      input after_static_reference static_tree Hstatic_body)
    as [static_trees [_ Hstatic_items]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend
        (descend
          (descend path (AtNonterminal "effect_expression"))
          (AtSequence 0))
        (AtNonterminal "static_reference")) 0
      (ENonterminal "qualified_name")
      [EOptional (ENonterminal "static_arguments")]
      input after_static_reference static_trees Hstatic_items)
    as [after_qualified_name
        [qualified_name_tree
          [static_tail_trees [Hqualified_name Hstatic_tail]]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend
        (descend
          (descend path (AtNonterminal "effect_expression"))
          (AtSequence 0))
        (AtNonterminal "static_reference")) 1
      (EOptional (ENonterminal "static_arguments")) []
      after_qualified_name after_static_reference
      static_tail_trees Hstatic_tail)
    as [after_static_arguments
        [static_arguments_tree [static_nil_trees [Hstatic_arguments Hstatic_nil]]]].
  pose proof
    (derives_sequence_nil_input_eq_rest
      phase1_surface_rules
      (descend
        (descend
          (descend path (AtNonterminal "effect_expression"))
          (AtSequence 0))
        (AtNonterminal "static_reference")) 2
      after_static_arguments after_static_reference
      static_nil_trees Hstatic_nil)
    as Hafter_static_arguments.
  destruct
    (phase1_surface_qualified_name_derivation_is_exact
      (descend
        (descend
          (descend
            (descend path (AtNonterminal "effect_expression"))
            (AtSequence 0))
          (AtNonterminal "static_reference"))
        (AtSequence 0))
      input after_qualified_name qualified_name_tree Hqualified_name)
    as [first_name [more_names Hinput]].
  destruct more_names as [| next_name more_names].
  - simpl in Hinput.
    destruct
      (derives_optional_input_cases
        phase1_surface_rules
        (descend
          (descend
            (descend
              (descend path (AtNonterminal "effect_expression"))
              (AtSequence 0))
            (AtNonterminal "static_reference"))
          (AtSequence 1))
        (ENonterminal "static_arguments")
        after_qualified_name after_static_arguments
        static_arguments_tree Hstatic_arguments)
      as [Hstatic_absent | Hstatic_present].
    + assert (Hafter_qualified_name :
        after_qualified_name = after_static_reference).
      {
        rewrite Hstatic_absent.
        exact Hafter_static_arguments.
      }
      destruct
        (derives_optional_input_cases
          phase1_surface_rules
          (descend
            (descend path (AtNonterminal "effect_expression"))
            (AtSequence 1))
          (ENonterminal "term_arguments")
          after_static_reference after_term_arguments
          term_arguments_tree Hterm_arguments)
        as [Hterm_absent | Hterm_present].
      * exists first_name, rest.
        split.
        -- rewrite Hinput.
           rewrite Hafter_qualified_name.
           rewrite Hterm_absent.
           rewrite Hafter_term_arguments.
           reflexivity.
        -- right.
           right.
           right.
           reflexivity.
      * destruct Hterm_present as [term_subtree Hterm_body].
        destruct
          (phase1_surface_term_arguments_derivation_starts_open_parenthesis
            (descend
              (descend
                (descend path (AtNonterminal "effect_expression"))
                (AtSequence 1))
              AtOptionalBody)
            after_static_reference after_term_arguments
            term_subtree Hterm_body)
          as [suffix Hafter_static_reference_prefix].
        exists first_name, (TLiteral "(" :: suffix).
        split.
        -- rewrite Hinput.
           rewrite Hafter_qualified_name.
           rewrite Hafter_static_reference_prefix.
           reflexivity.
        -- right.
           right.
           left.
           eexists.
           reflexivity.
    + destruct Hstatic_present as [static_subtree Hstatic_body_present].
      destruct
        (phase1_surface_static_arguments_derivation_starts_open_bracket
          (descend
            (descend
              (descend
                (descend
                  (descend path (AtNonterminal "effect_expression"))
                  (AtSequence 0))
                (AtNonterminal "static_reference"))
              (AtSequence 1))
            AtOptionalBody)
          after_qualified_name after_static_arguments
          static_subtree Hstatic_body_present)
        as [suffix Hafter_qualified_name_prefix].
      exists first_name, (TLiteral "[" :: suffix).
      split.
      * rewrite Hinput.
        rewrite Hafter_qualified_name_prefix.
        reflexivity.
      * right.
        left.
        eexists.
        reflexivity.
  - simpl in Hinput.
    exists first_name,
      (TLiteral "." ::
       TLexical "IDENTIFIER" next_name ::
       qualified_name_dot_tokens more_names after_qualified_name).
    split.
    + exact Hinput.
    + left.
      eexists.
      reflexivity.
Qed.

Lemma phase1_surface_effect_set_literal_lookup_exact :
  lookupRule "effect_set_literal" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "{"
        ; EOptional
            (ESequence
              [ ENonterminal "effect_expression"
              ; ERepetition
                  (ESequence
                    [ELiteral ","; ENonterminal "effect_expression"])
              ])
        ; ELiteral "}"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_effect_set_literal_derivation_commits_static_argument_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "effect_set_literal") input rest tree ->
    static_argument_decision input = Some (ChooseAlternative 3).
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "effect_set_literal"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_effect_set_literal_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal"))
      [ ELiteral "{"
      ; EOptional
          (ESequence
            [ ENonterminal "effect_expression"
            ; ERepetition
                (ESequence
                  [ELiteral ","; ENonterminal "effect_expression"])
            ])
      ; ELiteral "}"
      ]
      input rest subtree Hbody)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal")) 0
      (ELiteral "{")
      [ EOptional
          (ESequence
            [ ENonterminal "effect_expression"
            ; ERepetition
                (ESequence
                  [ELiteral ","; ENonterminal "effect_expression"])
            ])
      ; ELiteral "}"
      ]
      input rest trees Hitems)
    as [after_open [open_tree [tail_trees [Hopen Htail]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "effect_set_literal"))
        (AtSequence 0))
      "{" input after_open open_tree Hopen)
    as [open_tail [Hinput [Hafter_open _]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal")) 1
      (EOptional
        (ESequence
          [ ENonterminal "effect_expression"
          ; ERepetition
              (ESequence
                [ELiteral ","; ENonterminal "effect_expression"])
          ]))
      [ELiteral "}"]
      after_open rest tail_trees Htail)
    as [after_optional
        [optional_tree [close_trees [Hoptional Hclose_tail]]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "effect_set_literal")) 2
      (ELiteral "}") []
      after_optional rest close_trees Hclose_tail)
    as [after_close [close_tree [nil_trees [Hclose Hnil]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "effect_set_literal"))
        (AtSequence 2))
      "}" after_optional after_close close_tree Hclose)
    as [close_tail [Hafter_optional [_ _]]].
  destruct
    (derives_optional_input_cases
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "effect_set_literal"))
        (AtSequence 1))
      (ESequence
        [ ENonterminal "effect_expression"
        ; ERepetition
            (ESequence
              [ELiteral ","; ENonterminal "effect_expression"])
        ])
      after_open after_optional optional_tree Hoptional)
    as [Hoptional_absent | Hoptional_present].
  - rewrite Hinput.
    rewrite <- Hafter_open.
    rewrite Hoptional_absent.
    rewrite Hafter_optional.
    apply static_argument_empty_brace_tail_commits_effect_set.
  - destruct Hoptional_present as [optional_subtree Hoptional_body].
    destruct
      (derives_sequence_expression_exposes_items
        phase1_surface_rules
        (descend
          (descend
            (descend path (AtNonterminal "effect_set_literal"))
            (AtSequence 1))
          AtOptionalBody)
        [ ENonterminal "effect_expression"
        ; ERepetition
            (ESequence
              [ELiteral ","; ENonterminal "effect_expression"])
        ]
        after_open after_optional optional_subtree Hoptional_body)
      as [optional_trees [_ Hoptional_items]].
    destruct
      (derives_sequence_cons_exposes_head
        phase1_surface_rules
        (descend
          (descend
            (descend path (AtNonterminal "effect_set_literal"))
            (AtSequence 1))
          AtOptionalBody) 0
        (ENonterminal "effect_expression")
        [ ERepetition
            (ESequence
              [ELiteral ","; ENonterminal "effect_expression"])
        ]
        after_open after_optional optional_trees Hoptional_items)
      as [after_effect_expression
          [effect_expression_tree
            [optional_tail_trees [Heffect_expression Hrepetition_tail]]]].
    destruct
      (derives_sequence_cons_exposes_head
        phase1_surface_rules
        (descend
          (descend
            (descend path (AtNonterminal "effect_set_literal"))
            (AtSequence 1))
          AtOptionalBody) 1
        (ERepetition
          (ESequence
            [ELiteral ","; ENonterminal "effect_expression"]))
        []
        after_effect_expression after_optional
        optional_tail_trees Hrepetition_tail)
      as [after_repetition
          [repetition_tree [optional_nil_trees [Hrepetition Hoptional_nil]]]].
    pose proof
      (derives_sequence_nil_input_eq_rest
        phase1_surface_rules
        (descend
          (descend
            (descend path (AtNonterminal "effect_set_literal"))
            (AtSequence 1))
          AtOptionalBody) 2
        after_repetition after_optional
        optional_nil_trees Hoptional_nil)
      as Hafter_repetition.
    destruct
      (phase1_surface_effect_expression_identifier_tail_classification
        (descend
          (descend
            (descend
              (descend path (AtNonterminal "effect_set_literal"))
              (AtSequence 1))
            AtOptionalBody)
          (AtSequence 0))
        after_open after_effect_expression
        effect_expression_tree Heffect_expression)
      as [first_name [tail [Hafter_open_prefix Htail_classification]]].
    rewrite Hinput.
    rewrite <- Hafter_open.
    rewrite Hafter_open_prefix.
    destruct Htail_classification as
      [[suffix Hdot] |
       [[suffix Hbracket] |
        [[suffix Hparen] | Htail_rest]]].
    + rewrite Hdot.
      apply static_argument_brace_other_separator_tail_commits_effect_set.
      reflexivity.
    + rewrite Hbracket.
      apply static_argument_brace_other_separator_tail_commits_effect_set.
      reflexivity.
    + rewrite Hparen.
      apply static_argument_brace_other_separator_tail_commits_effect_set.
      reflexivity.
    + rewrite Htail_rest.
      destruct
        (derives_repetition_expression_exposes_body
          phase1_surface_rules
          (descend
            (descend
              (descend
                (descend path (AtNonterminal "effect_set_literal"))
                (AtSequence 1))
              AtOptionalBody)
            (AtSequence 1))
          (ESequence
            [ELiteral ","; ENonterminal "effect_expression"])
          after_effect_expression after_repetition
          repetition_tree Hrepetition)
        as [repetition_trees [_ Hrepetition_body]].
      destruct
        (derives_repetition_input_cases
          phase1_surface_rules
          (descend
            (descend
              (descend
                (descend path (AtNonterminal "effect_set_literal"))
                (AtSequence 1))
              AtOptionalBody)
            (AtSequence 1))
          (ESequence
            [ELiteral ","; ENonterminal "effect_expression"])
          after_effect_expression after_repetition
          repetition_trees Hrepetition_body)
        as [Hrepetition_empty | Hrepetition_present].
      * rewrite Hrepetition_empty.
        rewrite Hafter_repetition.
        rewrite Hafter_optional.
        apply static_argument_brace_other_separator_tail_commits_effect_set.
        reflexivity.
      * destruct Hrepetition_present
          as [middle [head_tree [tail_trees [Hhead _]]]].
        destruct
          (phase1_surface_sequence_literal_prefix
            (descend
              (descend
                (descend
                  (descend
                    (descend path (AtNonterminal "effect_set_literal"))
                    (AtSequence 1))
                  AtOptionalBody)
                (AtSequence 1))
              AtRepetitionBody)
            "," [ENonterminal "effect_expression"]
            after_effect_expression middle head_tree Hhead)
          as [suffix Hcomma].
        rewrite Hcomma.
        apply static_argument_brace_other_separator_tail_commits_effect_set.
        reflexivity.
Qed.
