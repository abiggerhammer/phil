From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacySimpleResolvers.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic soundness foundation for the seven simple resolver sites used by
  the final PHIL-SURFACE-DETERM-001 oracle bridge.

  The earlier resolver tranche checked the path/token decision functions and
  their exact certificate coverage.  Here we connect the reserved-prefix
  decisions to arbitrary ordinary derivations, and generalize the trailing-
  comma commitments from examples to arbitrary token tails.
*)

Lemma derives_nonterminal_exposes_body :
  forall rules path name input rest tree,
    Derives rules path (ENonterminal name) input rest tree ->
    exists body subtree,
      lookupRule name rules = Some body /\
      tree = PTNonterminal name subtree /\
      Derives rules (descend path (AtNonterminal name))
        body input rest subtree.
Proof.
  intros rules path name input rest tree Hderive.
  inversion Hderive; subst.
  do 2 eexists.
  repeat split; eauto.
Qed.

Lemma derives_sequence_expression_exposes_items :
  forall rules path items input rest tree,
    Derives rules path (ESequence items) input rest tree ->
    exists trees,
      tree = PTSequence trees /\
      DerivesSequence rules path 0 items input rest trees.
Proof.
  intros rules path items input rest tree Hderive.
  inversion Hderive; subst.
  eexists.
  split; eauto.
Qed.

Lemma derives_sequence_cons_exposes_head :
  forall rules path index item items input rest trees,
    DerivesSequence rules path index (item :: items) input rest trees ->
    exists middle tree tail_trees,
      Derives rules (descend path (AtSequence index))
        item input middle tree /\
      DerivesSequence rules path (S index)
        items middle rest tail_trees.
Proof.
  intros rules path index item items input rest trees Hderive.
  inversion Hderive; subst.
  do 3 eexists.
  split; eauto.
Qed.

Lemma phase1_surface_identifier_lookup_exact :
  lookupRule "identifier" phase1_surface_rules =
    Some (ELexicalClass "IDENTIFIER").
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_identifier_derivation_is_exact :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "identifier")
      input rest tree ->
    exists lexeme tail,
      input = TLexical "IDENTIFIER" lexeme :: tail /\
      rest = tail.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "identifier" input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_identifier_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (lexical_derivation_is_exact
      phase1_surface_rules
      (descend path (AtNonterminal "identifier"))
      "IDENTIFIER" input rest subtree Hbody)
    as [lexeme [tail [Hinput [Hrest _]]]].
  exists lexeme, tail.
  split; assumption.
Qed.

Lemma derives_sequence_literal_then_identifier_prefix :
  forall path literal tail_items input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        (ELiteral literal :: ENonterminal "identifier" :: tail_items))
      input rest tree ->
    exists lexeme suffix,
      input =
        TLiteral literal :: TLexical "IDENTIFIER" lexeme :: suffix.
Proof.
  intros path literal tail_items input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      (ELiteral literal :: ENonterminal "identifier" :: tail_items)
      input rest tree Hderive)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 0
      (ELiteral literal)
      (ENonterminal "identifier" :: tail_items)
      input rest trees Hitems)
    as [middle [literal_tree [tail_trees [Hliteral Htail]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 0))
      literal input middle literal_tree Hliteral)
    as [after_literal [Hinput [Hmiddle _]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 1
      (ENonterminal "identifier") tail_items
      middle rest tail_trees Htail)
    as [after_identifier [identifier_tree [rest_trees [Hidentifier _]]]].
  destruct
    (phase1_surface_identifier_derivation_is_exact
      (descend path (AtSequence 1))
      middle after_identifier identifier_tree Hidentifier)
    as [lexeme [suffix [Hidentifier_input _]]].
  exists lexeme, suffix.
  rewrite Hinput.
  rewrite <- Hmiddle.
  rewrite Hidentifier_input.
  reflexivity.
Qed.

Lemma derives_sequence_two_literals_prefix :
  forall path first_literal second_literal tail_items input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        (ELiteral first_literal :: ELiteral second_literal :: tail_items))
      input rest tree ->
    exists suffix,
      input =
        TLiteral first_literal :: TLiteral second_literal :: suffix.
Proof.
  intros path first_literal second_literal tail_items input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      (ELiteral first_literal :: ELiteral second_literal :: tail_items)
      input rest tree Hderive)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 0
      (ELiteral first_literal)
      (ELiteral second_literal :: tail_items)
      input rest trees Hitems)
    as [middle [first_tree [tail_trees [Hfirst Htail]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 0))
      first_literal input middle first_tree Hfirst)
    as [after_first [Hinput [Hmiddle _]]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 1
      (ELiteral second_literal) tail_items
      middle rest tail_trees Htail)
    as [after_second [second_tree [rest_trees [Hsecond _]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 1))
      second_literal middle after_second second_tree Hsecond)
    as [suffix [Hsecond_input [_ _]]].
  exists suffix.
  rewrite Hinput.
  rewrite <- Hmiddle.
  rewrite Hsecond_input.
  reflexivity.
Qed.

Lemma phase1_surface_provider_contract_body_prefix :
  exists tail_items,
    lookupRule "provider_contract_decl" phase1_surface_rules =
      Some
        (ESequence
          (ELiteral "provider" ::
           ENonterminal "identifier" ::
           tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Lemma phase1_surface_provider_implementation_body_prefix :
  exists tail_items,
    lookupRule "provider_implementation_decl" phase1_surface_rules =
      Some
        (ESequence
          (ELiteral "provider" ::
           ELiteral "implementation" ::
           tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Definition phase1_surface_declaration_items : list EbnfExpression :=
  match lookupRule "declaration" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Lemma phase1_surface_declaration_lookup_exact :
  lookupRule "declaration" phase1_surface_rules =
    Some (EAlternative phase1_surface_declaration_items).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_declaration_branch_six_exact :
  nth_error phase1_surface_declaration_items 6 =
    Some (ENonterminal "provider_contract_decl").
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_declaration_branch_seven_exact :
  nth_error phase1_surface_declaration_items 7 =
    Some (ENonterminal "provider_implementation_decl").
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem provider_contract_derivation_commits_branch_six :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "provider_contract_decl") input rest tree ->
    provider_declaration_decision input =
      Some (ChooseAlternative 6).
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "provider_contract_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  destruct phase1_surface_provider_contract_body_prefix
    as [tail_items Hknown].
  rewrite Hknown in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_literal_then_identifier_prefix
      (descend path (AtNonterminal "provider_contract_decl"))
      "provider" tail_items input rest subtree Hbody)
    as [lexeme [suffix Hinput]].
  subst input.
  reflexivity.
Qed.

Theorem provider_implementation_derivation_commits_branch_seven :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "provider_implementation_decl") input rest tree ->
    provider_declaration_decision input =
      Some (ChooseAlternative 7).
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "provider_implementation_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  destruct phase1_surface_provider_implementation_body_prefix
    as [tail_items Hknown].
  rewrite Hknown in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_two_literals_prefix
      (descend path (AtNonterminal "provider_implementation_decl"))
      "provider" "implementation" tail_items
      input rest subtree Hbody)
    as [suffix Hinput].
  subst input.
  reflexivity.
Qed.

Definition phase1_surface_generic_requirement_items : list EbnfExpression :=
  match lookupRule "generic_requirement" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Lemma phase1_surface_generic_requirement_lookup_exact :
  lookupRule "generic_requirement" phase1_surface_rules =
    Some (EAlternative phase1_surface_generic_requirement_items).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_generic_requirement_branch_four_prefix :
  exists tail_items,
    nth_error phase1_surface_generic_requirement_items 4 =
      Some
        (ESequence
          (ELiteral "boundary" ::
           ENonterminal "identifier" ::
           tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Lemma phase1_surface_generic_requirement_branch_eight_prefix :
  exists tail_items,
    nth_error phase1_surface_generic_requirement_items 8 =
      Some
        (ESequence
          (ELiteral "boundary" ::
           ELiteral "representation" ::
           tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Theorem generic_boundary_name_derivation_commits_branch_four :
  forall path tail_items input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        (ELiteral "boundary" ::
         ENonterminal "identifier" ::
         tail_items))
      input rest tree ->
    generic_requirement_decision input =
      Some (ChooseAlternative 4).
Proof.
  intros path tail_items input rest tree Hderive.
  destruct
    (derives_sequence_literal_then_identifier_prefix
      path "boundary" tail_items input rest tree Hderive)
    as [lexeme [suffix Hinput]].
  subst input.
  reflexivity.
Qed.

Theorem generic_boundary_representation_derivation_commits_branch_eight :
  forall path tail_items input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        (ELiteral "boundary" ::
         ELiteral "representation" ::
         tail_items))
      input rest tree ->
    generic_requirement_decision input =
      Some (ChooseAlternative 8).
Proof.
  intros path tail_items input rest tree Hderive.
  destruct
    (derives_sequence_two_literals_prefix
      path "boundary" "representation" tail_items
      input rest tree Hderive)
    as [suffix Hinput].
  subst input.
  reflexivity.
Qed.

Theorem provider_declaration_decision_contract_tail :
  forall lexeme tail,
    provider_declaration_decision
      (TLiteral "provider" ::
       TLexical "IDENTIFIER" lexeme :: tail) =
    Some (ChooseAlternative 6).
Proof.
  reflexivity.
Qed.

Theorem provider_declaration_decision_implementation_tail :
  forall tail,
    provider_declaration_decision
      (TLiteral "provider" ::
       TLiteral "implementation" :: tail) =
    Some (ChooseAlternative 7).
Proof.
  reflexivity.
Qed.

Theorem generic_requirement_decision_boundary_name_tail :
  forall lexeme tail,
    generic_requirement_decision
      (TLiteral "boundary" ::
       TLexical "IDENTIFIER" lexeme :: tail) =
    Some (ChooseAlternative 4).
Proof.
  reflexivity.
Qed.

Theorem generic_requirement_decision_boundary_representation_tail :
  forall tail,
    generic_requirement_decision
      (TLiteral "boundary" ::
       TLiteral "representation" :: tail) =
    Some (ChooseAlternative 8).
Proof.
  reflexivity.
Qed.

Theorem trailing_comma_decision_identifier_tail_continues :
  forall lexeme tail,
    trailing_comma_repeat_decision
      (TLiteral "," :: TLexical "IDENTIFIER" lexeme :: tail) =
    Some ChooseRepetitionContinue.
Proof.
  reflexivity.
Qed.

Theorem trailing_comma_decision_close_tail_stops :
  forall tail,
    trailing_comma_repeat_decision (TLiteral "}" :: tail) =
    Some ChooseRepetitionStop.
Proof.
  reflexivity.
Qed.

Theorem trailing_comma_decision_trailing_close_tail_stops :
  forall tail,
    trailing_comma_repeat_decision
      (TLiteral "," :: TLiteral "}" :: tail) =
    Some ChooseRepetitionStop.
Proof.
  reflexivity.
Qed.

Lemma path_has_suffix_descended_nonterminal :
  forall path name,
    path_has_suffixb
      (descend path (AtNonterminal name))
      [AtNonterminal name] = true.
Proof.
  intros path name.
  unfold path_has_suffixb, descend.
  rewrite List.rev_app_distr.
  simpl.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma phase1_surface_simple_resolver_provider_path :
  forall path input decision,
    provider_declaration_decision input = Some decision ->
    phase1_surface_simple_resolver
      (descend path (AtNonterminal "declaration")) input =
      Some decision.
Proof.
  intros path input decision Hdecision.
  unfold phase1_surface_simple_resolver.
  assert (Hsuffix :
    path_has_suffixb
      (descend path (AtNonterminal "declaration"))
      provider_declaration_suffix = true).
  {
    unfold provider_declaration_suffix.
    apply path_has_suffix_descended_nonterminal.
  }
  rewrite Hsuffix.
  exact Hdecision.
Qed.

Lemma phase1_surface_simple_resolver_generic_requirement_path :
  forall path input decision,
    generic_requirement_decision input = Some decision ->
    phase1_surface_simple_resolver
      (descend path (AtNonterminal "generic_requirement")) input =
      Some decision.
Proof.
  intros path input decision Hdecision.
  unfold phase1_surface_simple_resolver.
  assert (Hprovider_suffix :
    path_has_suffixb
      (descend path (AtNonterminal "generic_requirement"))
      provider_declaration_suffix = false).
  {
    unfold provider_declaration_suffix, path_has_suffixb, descend.
    rewrite List.rev_app_distr.
    simpl.
    reflexivity.
  }
  assert (Hgeneric_suffix :
    path_has_suffixb
      (descend path (AtNonterminal "generic_requirement"))
      generic_requirement_suffix = true).
  {
    unfold generic_requirement_suffix.
    apply path_has_suffix_descended_nonterminal.
  }
  rewrite Hprovider_suffix, Hgeneric_suffix.
  exact Hdecision.
Qed.
