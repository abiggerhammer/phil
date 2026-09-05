From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyStructuralScannerSoundness
  GrammarDeterminacyParenthesisNeutralSoundness
  GrammarDeterminacyQualifiedNameSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic soundness for the parenthesis-led static_argument overlap.

  On a leading "(", nonreference_type_expression can only reach tuple_type,
  whose first type_expression is followed by a top-level comma.  A
  static_value_expression can only reach the parenthesized
  static_nonreference_primary_expression, whose inner static value is followed
  by the matching close.  The parenthesis-neutral foundation supplies the
  neutral inner prefixes and the structural scanner commits branches 0 and 2.
*)

Lemma derives_sequence_literal_head_starts :
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

Lemma derives_sequence_nonterminal_head_exposes :
  forall path name tail_items input rest tree,
    Derives phase1_surface_rules path
      (ESequence (ENonterminal name :: tail_items))
      input rest tree ->
    exists head_path middle head_tree,
      Derives phase1_surface_rules head_path
        (ENonterminal name) input middle head_tree.
Proof.
  intros path name tail_items input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      (ENonterminal name :: tail_items)
      input rest tree Hderive)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 0
      (ENonterminal name) tail_items
      input rest trees Hitems)
    as [middle [head_tree [tail_trees [Hhead _]]]].
  exists (descend path (AtSequence 0)), middle, head_tree.
  exact Hhead.
Qed.

Lemma derives_nonterminal_alias_exposes :
  forall path outer_name inner_name input rest tree,
    lookupRule outer_name phase1_surface_rules =
      Some (ENonterminal inner_name) ->
    Derives phase1_surface_rules path
      (ENonterminal outer_name) input rest tree ->
    exists inner_path inner_tree,
      Derives phase1_surface_rules inner_path
        (ENonterminal inner_name) input rest inner_tree.
Proof.
  intros path outer_name inner_name input rest tree Hknown Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path outer_name input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hknown in Hlookup.
  inversion Hlookup; subst body.
  exists (descend path (AtNonterminal outer_name)), subtree.
  exact Hbody.
Qed.

Lemma derives_nonterminal_sequence_nonterminal_head :
  forall path outer_name head_name tail_items input rest tree,
    lookupRule outer_name phase1_surface_rules =
      Some (ESequence (ENonterminal head_name :: tail_items)) ->
    Derives phase1_surface_rules path
      (ENonterminal outer_name) input rest tree ->
    exists head_path middle head_tree,
      Derives phase1_surface_rules head_path
        (ENonterminal head_name) input middle head_tree.
Proof.
  intros path outer_name head_name tail_items input rest tree Hknown Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path outer_name input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hknown in Hlookup.
  inversion Hlookup; subst body.
  eapply derives_sequence_nonterminal_head_exposes.
  exact Hbody.
Qed.

Lemma derives_nonterminal_lexical_starts :
  forall path name class_name input rest tree,
    lookupRule name phase1_surface_rules =
      Some (ELexicalClass class_name) ->
    Derives phase1_surface_rules path
      (ENonterminal name) input rest tree ->
    exists lexeme suffix,
      input = TLexical class_name lexeme :: suffix.
Proof.
  intros path name class_name input rest tree Hknown Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path name input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hknown in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (lexical_derivation_is_exact
      phase1_surface_rules
      (descend path (AtNonterminal name))
      class_name input rest subtree Hbody)
    as [lexeme [suffix [Hinput [_ _]]]].
  exists lexeme, suffix.
  exact Hinput.
Qed.

Lemma derives_nonterminal_sequence_literal_head_starts :
  forall path name literal tail_items input rest tree,
    lookupRule name phase1_surface_rules =
      Some (ESequence (ELiteral literal :: tail_items)) ->
    Derives phase1_surface_rules path
      (ENonterminal name) input rest tree ->
    exists suffix,
      input = TLiteral literal :: suffix.
Proof.
  intros path name literal tail_items input rest tree Hknown Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path name input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hknown in Hlookup.
  inversion Hlookup; subst body.
  eapply derives_sequence_literal_head_starts.
  exact Hbody.
Qed.

Lemma derives_sequence_open_neutral_nonterminal_separator_prefix :
  forall name path separator tail_items input rest tree,
    (forall npath ninput nrest ntree,
      Derives phase1_surface_rules npath
        (ENonterminal name) ninput nrest ntree ->
      exists consumed,
        ninput = List.app consumed nrest /\
        parenthesis_neutral_scan 0 consumed = Some 0) ->
    Derives phase1_surface_rules path
      (ESequence
        (ELiteral "(" ::
         ENonterminal name ::
         ELiteral separator ::
         tail_items))
      input rest tree ->
    exists consumed suffix,
      input =
        TLiteral "(" ::
        (consumed ++ TLiteral separator :: suffix) /\
      parenthesis_neutral_scan 0 consumed = Some 0.
Proof.
  intros name path separator tail_items input rest tree Hneutral_name Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      (ELiteral "(" ::
       ENonterminal name ::
       ELiteral separator ::
       tail_items)
      input rest tree Hderive)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 0
      (ELiteral "(")
      (ENonterminal name :: ELiteral separator :: tail_items)
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
      (ENonterminal name)
      (ELiteral separator :: tail_items)
      after_open rest tail_trees Htail)
    as [after_inner
        [inner_tree [remaining_trees [Hinner Hremaining]]]].
  destruct
    (Hneutral_name
      (descend path (AtSequence 1))
      after_open after_inner inner_tree Hinner)
    as [consumed [Hinner_input Hneutral]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 2
      (ELiteral separator) tail_items
      after_inner rest remaining_trees Hremaining)
    as [after_separator
        [separator_tree [separator_tail_trees [Hseparator _]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 2))
      separator after_inner after_separator separator_tree Hseparator)
    as [suffix [Hseparator_input [_ _]]].
  exists consumed, suffix.
  split.
  - rewrite Hinput.
    rewrite <- Hafter_open.
    rewrite Hinner_input.
    rewrite Hseparator_input.
    reflexivity.
  - exact Hneutral.
Qed.

Lemma phase1_surface_uint_type_lookup_exact :
  lookupRule "uint_type" phase1_surface_rules =
    Some (ELexicalClass "UINT_TYPE").
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_sint_type_lookup_exact :
  lookupRule "sint_type" phase1_surface_rules =
    Some (ELexicalClass "SINT_TYPE").
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_float_type_lookup_exact :
  lookupRule "float_type" phase1_surface_rules =
    Some (EAlternative [ELiteral "F32"; ELiteral "F64"]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_float_type_open_derivation_impossible :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "float_type") input rest tree ->
    input = TLiteral "(" :: tail ->
    False.
Proof.
  intros path input rest tree tail Hderive Hinput_open.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "float_type" input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_float_type_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "float_type"))
      [ELiteral "F32"; ELiteral "F64"]
      input rest subtree Hbody)
    as [index [item [branch_tree [Hnth [_ Hbranch]]]]].
  destruct index as [| index].
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "F32" input rest branch_tree Hbranch)
      as [suffix [Hstart _]].
    rewrite Hinput_open in Hstart.
    discriminate Hstart.
  - destruct index as [| index].
    + vm_compute in Hnth.
      inversion Hnth; subst item.
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "F64" input rest branch_tree Hbranch)
        as [suffix [Hstart _]].
      rewrite Hinput_open in Hstart.
      discriminate Hstart.
    + destruct index; vm_compute in Hnth; discriminate Hnth.
Qed.

Lemma phase1_surface_integer_literal_lookup_exact :
  lookupRule "integer_literal" phase1_surface_rules =
    Some (ELexicalClass "DECIMAL_INTEGER").
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_refinement_type_lookup_prefix :
  exists tail_items,
    lookupRule "refinement_type" phase1_surface_rules =
      Some (ESequence (ELiteral "{" :: tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Lemma phase1_surface_tuple_type_lookup_prefix :
  exists tail_items,
    lookupRule "tuple_type" phase1_surface_rules =
      Some
        (ESequence
          (ELiteral "(" ::
           ENonterminal "type_expression" ::
           ELiteral "," ::
           tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Theorem phase1_surface_tuple_type_derivation_commits_static_argument_tuple_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "tuple_type") input rest tree ->
    static_argument_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_tuple_type_lookup_prefix
    as [tail_items Hknown].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "tuple_type"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite Hknown in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_open_neutral_nonterminal_separator_prefix
      "type_expression"
      (descend path (AtNonterminal "tuple_type"))
      "," tail_items input rest subtree
      phase1_surface_type_expression_derivation_is_parenthesis_neutral
      Hbody)
    as [consumed [suffix [Hinput Hneutral]]].
  rewrite Hinput.
  apply static_argument_neutral_comma_commits_tuple_type.
  exact Hneutral.
Qed.

Definition phase1_surface_nonreference_type_expression_items :
  list EbnfExpression :=
  match lookupRule "nonreference_type_expression" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Lemma phase1_surface_nonreference_type_expression_lookup_exact :
  lookupRule "nonreference_type_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_nonreference_type_expression_items).
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_nonreference_type_expression_open_derivation_commits_static_argument_tuple_branch :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    input = TLiteral "(" :: tail ->
    static_argument_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree tail Hderive Hinput_open.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "nonreference_type_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_nonreference_type_expression_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "nonreference_type_expression"))
      phase1_surface_nonreference_type_expression_items
      input rest subtree Hbody)
    as [index [item [branch_tree [Hnth [_ Hbranch]]]]].
  destruct index as [| index].
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "Unit" input rest branch_tree Hbranch)
      as [suffix [Hstart _]].
    rewrite Hinput_open in Hstart.
    discriminate Hstart.
  - destruct index as [| index].
    + vm_compute in Hnth.
      inversion Hnth; subst item.
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "Bool" input rest branch_tree Hbranch)
        as [suffix [Hstart _]].
      rewrite Hinput_open in Hstart.
      discriminate Hstart.
    + destruct index as [| index].
      * vm_compute in Hnth.
        inversion Hnth; subst item.
        destruct
          (literal_derivation_is_exact
            phase1_surface_rules _ "Char" input rest branch_tree Hbranch)
          as [suffix [Hstart _]].
        rewrite Hinput_open in Hstart.
        discriminate Hstart.
      * destruct index as [| index].
        -- vm_compute in Hnth.
           inversion Hnth; subst item.
           destruct
             (literal_derivation_is_exact
               phase1_surface_rules _ "String" input rest branch_tree Hbranch)
             as [suffix [Hstart _]].
           rewrite Hinput_open in Hstart.
           discriminate Hstart.
        -- destruct index as [| index].
           ++ vm_compute in Hnth.
              inversion Hnth; subst item.
              destruct
                (derives_nonterminal_lexical_starts
                  _ "uint_type" "UINT_TYPE" input rest branch_tree
                  phase1_surface_uint_type_lookup_exact Hbranch)
                as [lexeme [suffix Hstart]].
              rewrite Hinput_open in Hstart.
              discriminate Hstart.
           ++ destruct index as [| index].
              ** vm_compute in Hnth.
                 inversion Hnth; subst item.
                 destruct
                   (derives_nonterminal_lexical_starts
                     _ "sint_type" "SINT_TYPE" input rest branch_tree
                     phase1_surface_sint_type_lookup_exact Hbranch)
                   as [lexeme [suffix Hstart]].
                 rewrite Hinput_open in Hstart.
                 discriminate Hstart.
              ** destruct index as [| index].
                 --- vm_compute in Hnth.
                     inversion Hnth; subst item.
                     exfalso.
                     eapply phase1_surface_float_type_open_derivation_impossible.
                     +++ exact Hbranch.
                     +++ exact Hinput_open.
                 --- destruct index as [| index].
                     +++ vm_compute in Hnth.
                         inversion Hnth; subst item.
                         destruct
                           (derives_sequence_literal_head_starts _ "Bytes" _
                             input rest branch_tree Hbranch)
                           as [suffix Hstart].
                         rewrite Hinput_open in Hstart.
                         discriminate Hstart.
                     +++ destruct index as [| index].
                         *** vm_compute in Hnth.
                             inversion Hnth; subst item.
                             destruct
                               (derives_sequence_literal_head_starts _ "Frame" _
                                 input rest branch_tree Hbranch)
                               as [suffix Hstart].
                             rewrite Hinput_open in Hstart.
                             discriminate Hstart.
                         *** destruct index as [| index].
                             ---- vm_compute in Hnth.
                                  inversion Hnth; subst item.
                                  destruct
                                    (derives_sequence_literal_head_starts _ "Proof" _
                                      input rest branch_tree Hbranch)
                                    as [suffix Hstart].
                                  rewrite Hinput_open in Hstart.
                                  discriminate Hstart.
                             ---- destruct index as [| index].
                                  ++++ vm_compute in Hnth.
                                       inversion Hnth; subst item.
                                       destruct
                                         (derives_sequence_literal_head_starts _ "Validated" _
                                           input rest branch_tree Hbranch)
                                         as [suffix Hstart].
                                       rewrite Hinput_open in Hstart.
                                       discriminate Hstart.
                                  ++++ destruct index as [| index].
                                       ----- vm_compute in Hnth.
                                            inversion Hnth; subst item.
                                            destruct phase1_surface_refinement_type_lookup_prefix
                                              as [tail_items Hrefinement].
                                            destruct
                                              (derives_nonterminal_sequence_literal_head_starts
                                                _ "refinement_type" "{" tail_items
                                                input rest branch_tree Hrefinement Hbranch)
                                              as [suffix Hstart].
                                            rewrite Hinput_open in Hstart.
                                            discriminate Hstart.
                                       ----- destruct index as [| index].
                                            ***** vm_compute in Hnth.
                                                  inversion Hnth; subst item.
                                                  eapply phase1_surface_tuple_type_derivation_commits_static_argument_tuple_branch.
                                                  exact Hbranch.
                                            ***** destruct index; vm_compute in Hnth; discriminate Hnth.
Qed.

Lemma phase1_surface_static_value_expression_lookup_exact :
  lookupRule "static_value_expression" phase1_surface_rules =
    Some (ENonterminal "static_additive_expression").
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_static_additive_expression_lookup_prefix :
  exists tail_items,
    lookupRule "static_additive_expression" phase1_surface_rules =
      Some
        (ESequence
          (ENonterminal "static_multiplicative_expression" :: tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Lemma phase1_surface_static_multiplicative_expression_lookup_prefix :
  exists tail_items,
    lookupRule "static_multiplicative_expression" phase1_surface_rules =
      Some
        (ESequence
          (ENonterminal "static_postfix_expression" :: tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Lemma phase1_surface_static_value_expression_exposes_postfix_head :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "static_value_expression") input rest tree ->
    exists postfix_path middle postfix_tree,
      Derives phase1_surface_rules postfix_path
        (ENonterminal "static_postfix_expression")
        input middle postfix_tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_alias_exposes
      path "static_value_expression" "static_additive_expression"
      input rest tree
      phase1_surface_static_value_expression_lookup_exact Hderive)
    as [additive_path [additive_tree Hadditive]].
  destruct phase1_surface_static_additive_expression_lookup_prefix
    as [additive_tail Hadditive_lookup].
  destruct
    (derives_nonterminal_sequence_nonterminal_head
      additive_path
      "static_additive_expression" "static_multiplicative_expression"
      additive_tail input rest additive_tree
      Hadditive_lookup Hadditive)
    as [multiplicative_path
        [after_multiplicative [multiplicative_tree Hmultiplicative]]].
  destruct phase1_surface_static_multiplicative_expression_lookup_prefix
    as [multiplicative_tail Hmultiplicative_lookup].
  destruct
    (derives_nonterminal_sequence_nonterminal_head
      multiplicative_path
      "static_multiplicative_expression" "static_postfix_expression"
      multiplicative_tail input after_multiplicative multiplicative_tree
      Hmultiplicative_lookup Hmultiplicative)
    as [postfix_path [middle [postfix_tree Hpostfix]]].
  exists postfix_path, middle, postfix_tree.
  exact Hpostfix.
Qed.

Definition phase1_surface_static_postfix_expression_items :
  list EbnfExpression :=
  match lookupRule "static_postfix_expression" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Lemma phase1_surface_static_postfix_expression_lookup_exact :
  lookupRule "static_postfix_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_static_postfix_expression_items).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_static_postfix_open_derivation_exposes_nonreference_primary :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "static_postfix_expression") input rest tree ->
    input = TLiteral "(" :: tail ->
    exists primary_path middle primary_tree,
      Derives phase1_surface_rules primary_path
        (ENonterminal "static_nonreference_primary_expression")
        input middle primary_tree.
Proof.
  intros path input rest tree tail Hderive Hinput_open.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "static_postfix_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_static_postfix_expression_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "static_postfix_expression"))
      phase1_surface_static_postfix_expression_items
      input rest subtree Hbody)
    as [index [item [branch_tree [Hnth [_ Hbranch]]]]].
  destruct index as [| index].
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    destruct
      (derives_sequence_nonterminal_head_exposes
        _ "qualified_name" _ input rest branch_tree Hbranch)
      as [qualified_path [middle [qualified_tree Hqualified]]].
    destruct
      (phase1_surface_qualified_name_derivation_is_exact
        qualified_path input middle qualified_tree Hqualified)
      as [first_name [more_names Hqualified_input]].
    rewrite Hinput_open in Hqualified_input.
    discriminate Hqualified_input.
  - destruct index as [| index].
    + vm_compute in Hnth.
      inversion Hnth; subst item.
      destruct
        (derives_sequence_nonterminal_head_exposes
          _ "static_nonreference_primary_expression" _
          input rest branch_tree Hbranch)
        as [primary_path [middle [primary_tree Hprimary]]].
      exists primary_path, middle, primary_tree.
      exact Hprimary.
    + destruct index; vm_compute in Hnth; discriminate Hnth.
Qed.

Definition phase1_surface_static_nonreference_primary_expression_items :
  list EbnfExpression :=
  match lookupRule "static_nonreference_primary_expression" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Lemma phase1_surface_static_nonreference_primary_expression_lookup_exact :
  lookupRule "static_nonreference_primary_expression" phase1_surface_rules =
    Some
      (EAlternative
        phase1_surface_static_nonreference_primary_expression_items).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_static_nonreference_primary_open_derivation_exposes_parenthesized :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "static_nonreference_primary_expression")
      input rest tree ->
    input = TLiteral "(" :: tail ->
    exists parenthesized_path parenthesized_tree,
      Derives phase1_surface_rules parenthesized_path
        (ESequence
          [ ELiteral "("
          ; ENonterminal "static_value_expression"
          ; ELiteral ")"
          ])
        input rest parenthesized_tree.
Proof.
  intros path input rest tree tail Hderive Hinput_open.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "static_nonreference_primary_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_static_nonreference_primary_expression_lookup_exact
    in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "static_nonreference_primary_expression"))
      phase1_surface_static_nonreference_primary_expression_items
      input rest subtree Hbody)
    as [index [item [branch_tree [Hnth [_ Hbranch]]]]].
  destruct index as [| index].
  - vm_compute in Hnth.
    inversion Hnth; subst item.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "true" input rest branch_tree Hbranch)
      as [suffix [Hstart _]].
    rewrite Hinput_open in Hstart.
    discriminate Hstart.
  - destruct index as [| index].
    + vm_compute in Hnth.
      inversion Hnth; subst item.
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "false" input rest branch_tree Hbranch)
        as [suffix [Hstart _]].
      rewrite Hinput_open in Hstart.
      discriminate Hstart.
    + destruct index as [| index].
      * vm_compute in Hnth.
        inversion Hnth; subst item.
        destruct
          (literal_derivation_is_exact
            phase1_surface_rules _ "unit" input rest branch_tree Hbranch)
          as [suffix [Hstart _]].
        rewrite Hinput_open in Hstart.
        discriminate Hstart.
      * destruct index as [| index].
        -- vm_compute in Hnth.
           inversion Hnth; subst item.
           destruct
             (derives_nonterminal_lexical_starts
               _ "integer_literal" "DECIMAL_INTEGER"
               input rest branch_tree
               phase1_surface_integer_literal_lookup_exact Hbranch)
             as [lexeme [suffix Hstart]].
           rewrite Hinput_open in Hstart.
           discriminate Hstart.
        -- destruct index as [| index].
           ++ vm_compute in Hnth.
              inversion Hnth; subst item.
              exists
                (descend
                  (descend path
                    (AtNonterminal "static_nonreference_primary_expression"))
                  (AtAlternative 4)),
                branch_tree.
              exact Hbranch.
           ++ destruct index; vm_compute in Hnth; discriminate Hnth.
Qed.

Theorem phase1_surface_static_value_expression_open_derivation_commits_static_argument_value_branch :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "static_value_expression") input rest tree ->
    input = TLiteral "(" :: tail ->
    static_argument_decision input = Some (ChooseAlternative 2).
Proof.
  intros path input rest tree tail Hderive Hinput_open.
  destruct
    (phase1_surface_static_value_expression_exposes_postfix_head
      path input rest tree Hderive)
    as [postfix_path [after_postfix [postfix_tree Hpostfix]]].
  destruct
    (phase1_surface_static_postfix_open_derivation_exposes_nonreference_primary
      postfix_path input after_postfix postfix_tree tail
      Hpostfix Hinput_open)
    as [primary_path [after_primary [primary_tree Hprimary]]].
  destruct
    (phase1_surface_static_nonreference_primary_open_derivation_exposes_parenthesized
      primary_path input after_primary primary_tree tail
      Hprimary Hinput_open)
    as [parenthesized_path [parenthesized_tree Hparenthesized]].
  destruct
    (derives_sequence_open_neutral_nonterminal_separator_prefix
      "static_value_expression" parenthesized_path ")" []
      input after_primary parenthesized_tree
      phase1_surface_static_value_expression_derivation_is_parenthesis_neutral
      Hparenthesized)
    as [consumed [suffix [Hinput Hneutral]]].
  rewrite Hinput.
  apply static_argument_neutral_close_commits_static_value.
  exact Hneutral.
Qed.

Theorem phase1_surface_static_argument_parenthesis_structural_overlap_semantic_sound :
  (forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    input = TLiteral "(" :: tail ->
    static_argument_decision input = Some (ChooseAlternative 0)) /\
  (forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "static_value_expression") input rest tree ->
    input = TLiteral "(" :: tail ->
    static_argument_decision input = Some (ChooseAlternative 2)).
Proof.
  split.
  - exact
      phase1_surface_nonreference_type_expression_open_derivation_commits_static_argument_tuple_branch.
  - exact
      phase1_surface_static_value_expression_open_derivation_commits_static_argument_value_branch.
Qed.