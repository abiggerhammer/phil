From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolverSoundness
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyStructuralScannerSoundness
  GrammarDeterminacyContinuationSoundness
  GrammarDeterminacyDelimiterBalance
  GrammarDeterminacyQualifiedNameSoundness
  GrammarDeterminacyRelationNeutralSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic soundness for the final structural resolver family:
  proposition_atom relation commitment.

  A relation_proposition exposes a relation-neutral shift-expression prefix
  followed by an exact top-level relation operator, so the scanner must commit
  branch 0.  The nonrelation branches use the accepting continuation of
  proposition_atom; a computed FOLLOW certificate proves that every such
  continuation stops the relation scanner before it can wander into following
  syntax.
*)

Definition phase1_surface_proposition_atom_follow : list OverlapToken :=
  lookup_tokens "proposition_atom" phase1_surface_follow_facts.

Definition relation_follow_literal_stopsb (literal : string) : bool :=
  orb
    (proposition_atom_boundary_literalb literal)
    (andb
      (negb (delimiter_open_literalb literal))
      (delimiter_close_literalb literal)).

Definition relation_follow_token_stopsb (token : OverlapToken) : bool :=
  match token with
  | OverlapLiteral literal => relation_follow_literal_stopsb literal
  | OverlapEof => true
  | _ => false
  end.

Theorem phase1_surface_proposition_atom_follow_stops_relation_scan :
  forallb
    relation_follow_token_stopsb
    phase1_surface_proposition_atom_follow = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Opaque phase1_surface_proposition_atom_follow.

Lemma relation_continuation_lookahead_literal_cons :
  forall literal tail follow,
    continuation_lookahead_mem
      (TLiteral literal :: tail) follow =
    token_mem (OverlapLiteral literal) follow.
Proof.
  reflexivity.
Qed.

Lemma relation_continuation_lookahead_lexical_cons :
  forall class_name lexeme tail follow,
    continuation_lookahead_mem
      (TLexical class_name lexeme :: tail) follow =
    token_mem (OverlapLexicalClass class_name) follow.
Proof.
  reflexivity.
Qed.

Lemma relation_overlap_token_eqb_eq :
  forall first second,
    overlap_token_eqb first second = true ->
    first = second.
Proof.
  intros first second Heq.
  destruct first as [first | first | |];
    destruct second as [second | second | |];
    simpl in Heq; try discriminate; try reflexivity.
  - apply String.eqb_eq in Heq. subst second. reflexivity.
  - apply String.eqb_eq in Heq. subst second. reflexivity.
Qed.

Lemma relation_token_mem_true_in :
  forall token tokens,
    token_mem token tokens = true ->
    In token tokens.
Proof.
  intros token tokens.
  induction tokens as [| head tail IH]; intros Hmem.
  - discriminate Hmem.
  - simpl in Hmem.
    destruct (overlap_token_eqb token head) eqn:Heq.
    + apply relation_overlap_token_eqb_eq in Heq.
      subst head.
      left.
      reflexivity.
    + right.
      eapply IH.
      exact Hmem.
Qed.

Lemma phase1_surface_proposition_atom_follow_member_stops :
  forall token,
    token_mem token phase1_surface_proposition_atom_follow = true ->
    relation_follow_token_stopsb token = true.
Proof.
  intros token Hmem.
  apply relation_token_mem_true_in in Hmem.
  pose proof phase1_surface_proposition_atom_follow_stops_relation_scan
    as Hall.
  rewrite forallb_forall in Hall.
  exact (Hall token Hmem).
Qed.

Lemma relation_follow_literal_scan_false :
  forall literal tail,
    relation_follow_literal_stopsb literal = true ->
    relation_commit_scan 0 (TLiteral literal :: tail) = false.
Proof.
  intros literal tail Hstop.
  unfold relation_follow_literal_stopsb in Hstop.
  apply orb_true_iff in Hstop as [Hboundary | Hclose].
  - simpl.
    rewrite Hboundary.
    reflexivity.
  - apply andb_true_iff in Hclose as [Hopen Hclose].
    apply negb_true_iff in Hopen.
    simpl.
    destruct (proposition_atom_boundary_literalb literal) eqn:Hboundary.
    + reflexivity.
    + rewrite Hopen, Hclose.
      reflexivity.
Qed.

Theorem phase1_surface_proposition_atom_accepting_continuation_stops_relation_scan :
  forall input,
    continuation_lookahead_mem
      input phase1_surface_proposition_atom_follow = true ->
    relation_commit_scan 0 input = false.
Proof.
  intros input Hcontinuation.
  destruct input as [| token tail].
  - reflexivity.
  - destruct token as [literal | class_name lexeme].
    + rewrite relation_continuation_lookahead_literal_cons in Hcontinuation.
      pose proof
        (phase1_surface_proposition_atom_follow_member_stops
          (OverlapLiteral literal) Hcontinuation)
        as Hstop.
      simpl in Hstop.
      eapply relation_follow_literal_scan_false.
      exact Hstop.
    + rewrite relation_continuation_lookahead_lexical_cons in Hcontinuation.
      pose proof
        (phase1_surface_proposition_atom_follow_member_stops
          (OverlapLexicalClass class_name) Hcontinuation)
        as Hstop.
      simpl in Hstop.
      discriminate Hstop.
Qed.

Definition phase1_surface_relation_operator_items : list EbnfExpression :=
  match lookupRule "relation_operator" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Lemma phase1_surface_relation_operator_lookup_exact :
  lookupRule "relation_operator" phase1_surface_rules =
    Some (EAlternative phase1_surface_relation_operator_items).
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition relation_operator_expressionb
  (expression : EbnfExpression) : bool :=
  match expression with
  | ELiteral literal =>
      andb
        (negb (delimiter_open_literalb literal))
        (andb
          (negb (delimiter_close_literalb literal))
          (relation_operator_literalb literal))
  | _ => false
  end.

Theorem phase1_surface_relation_operator_items_are_exact :
  forallb
    relation_operator_expressionb
    phase1_surface_relation_operator_items = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Opaque phase1_surface_relation_operator_items.

Lemma phase1_surface_relation_operator_derivation_is_exact :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "relation_operator") input rest tree ->
    exists literal tail,
      input = TLiteral literal :: tail /\
      rest = tail /\
      delimiter_open_literalb literal = false /\
      delimiter_close_literalb literal = false /\
      relation_operator_literalb literal = true.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "relation_operator"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_relation_operator_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "relation_operator"))
      phase1_surface_relation_operator_items
      input rest subtree Hbody)
    as [index [item [branch_tree [Hnth [_ Hbranch]]]]].
  assert (Hin : In item phase1_surface_relation_operator_items).
  {
    eapply nth_error_In.
    exact Hnth.
  }
  pose proof phase1_surface_relation_operator_items_are_exact as Hall.
  rewrite forallb_forall in Hall.
  specialize (Hall item Hin).
  destruct item as
      [literal | class_name | name | items | items | body | body];
    simpl in Hall; try discriminate Hall.
  apply andb_true_iff in Hall as [Hopen Hall].
  apply negb_true_iff in Hopen.
  apply andb_true_iff in Hall as [Hclose Hoperator].
  apply negb_true_iff in Hclose.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "relation_operator"))
        (AtAlternative index))
      literal input rest branch_tree Hbranch)
    as [tail [Hinput [Hrest _]]].
  exists literal, tail.
  repeat split; assumption.
Qed.

Corollary phase1_surface_shift_expression_derivation_is_relation_neutral :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "shift_expression") input rest tree ->
    exists consumed,
      input = List.app consumed rest /\
      relation_neutral_scan 0 consumed = Some 0.
Proof.
  intros path input rest tree Hderive.
  eapply
    (phase1_surface_safe_nonterminal_derivation_is_relation_neutral
      path "shift_expression" input rest tree).
  - vm_compute.
    reflexivity.
  - exact Hderive.
Qed.

Lemma phase1_surface_relation_proposition_lookup_exact :
  lookupRule "relation_proposition" phase1_surface_rules =
    Some
      (ESequence
        [ ENonterminal "shift_expression"
        ; ENonterminal "relation_operator"
        ; ENonterminal "shift_expression"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_relation_proposition_derivation_sets_relation_scan_true :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "relation_proposition") input rest tree ->
    relation_commit_scan 0 input = true.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "relation_proposition"
      input rest tree Hderive)
    as [body [subtree [Hlookup [_ Hbody]]]].
  rewrite phase1_surface_relation_proposition_lookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "relation_proposition"))
      [ ENonterminal "shift_expression"
      ; ENonterminal "relation_operator"
      ; ENonterminal "shift_expression"
      ]
      input rest subtree Hbody)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "relation_proposition")) 0
      (ENonterminal "shift_expression")
      [ ENonterminal "relation_operator"
      ; ENonterminal "shift_expression"
      ]
      input rest trees Hitems)
    as [after_left [left_tree [tail_trees [Hleft Htail]]]].
  destruct
    (phase1_surface_shift_expression_derivation_is_relation_neutral
      (descend
        (descend path (AtNonterminal "relation_proposition"))
        (AtSequence 0))
      input after_left left_tree Hleft)
    as [prefix [Hinput Hneutral]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "relation_proposition")) 1
      (ENonterminal "relation_operator")
      [ENonterminal "shift_expression"]
      after_left rest tail_trees Htail)
    as [after_operator
        [operator_tree [right_trees [Hoperator Hright]]]].
  destruct
    (phase1_surface_relation_operator_derivation_is_exact
      (descend
        (descend path (AtNonterminal "relation_proposition"))
        (AtSequence 1))
      after_left after_operator operator_tree Hoperator)
    as [literal [operator_tail
      [Hafter_left [_ [Hopen [Hclose Hoperator_literal]]]]]].
  rewrite Hinput.
  rewrite Hafter_left.
  eapply relation_commit_scan_neutral_operator.
  - exact Hneutral.
  - exact Hopen.
  - exact Hclose.
  - exact Hoperator_literal.
Qed.

Theorem phase1_surface_relation_proposition_identifier_overlap_commits_relation :
  forall path input rest tree lexeme tail,
    Derives phase1_surface_rules path
      (ENonterminal "relation_proposition") input rest tree ->
    input = TLexical "IDENTIFIER" lexeme :: tail ->
    proposition_atom_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree lexeme tail Hderive Hinput.
  pose proof
    (phase1_surface_relation_proposition_derivation_sets_relation_scan_true
      path input rest tree Hderive)
    as Hscan.
  rewrite Hinput in Hscan.
  simpl in Hscan.
  rewrite Hinput.
  apply proposition_identifier_scan_true_commits_relation.
  exact Hscan.
Qed.

Theorem phase1_surface_relation_proposition_parenthesis_overlap_commits_relation :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "relation_proposition") input rest tree ->
    input = TLiteral "(" :: tail ->
    proposition_atom_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree tail Hderive Hinput.
  pose proof
    (phase1_surface_relation_proposition_derivation_sets_relation_scan_true
      path input rest tree Hderive)
    as Hscan.
  rewrite Hinput in Hscan.
  simpl in Hscan.
  rewrite Hinput.
  apply proposition_parenthesis_scan_true_commits_relation.
  exact Hscan.
Qed.

Theorem phase1_surface_relation_proposition_true_overlap_commits_relation :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "relation_proposition") input rest tree ->
    input = TLiteral "true" :: tail ->
    proposition_atom_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree tail Hderive Hinput.
  pose proof
    (phase1_surface_relation_proposition_derivation_sets_relation_scan_true
      path input rest tree Hderive)
    as Hscan.
  rewrite Hinput in Hscan.
  simpl in Hscan.
  rewrite Hinput.
  apply proposition_true_scan_true_commits_relation.
  exact Hscan.
Qed.

Theorem phase1_surface_relation_proposition_false_overlap_commits_relation :
  forall path input rest tree tail,
    Derives phase1_surface_rules path
      (ENonterminal "relation_proposition") input rest tree ->
    input = TLiteral "false" :: tail ->
    proposition_atom_decision input = Some (ChooseAlternative 0).
Proof.
  intros path input rest tree tail Hderive Hinput.
  pose proof
    (phase1_surface_relation_proposition_derivation_sets_relation_scan_true
      path input rest tree Hderive)
    as Hscan.
  rewrite Hinput in Hscan.
  simpl in Hscan.
  rewrite Hinput.
  apply proposition_false_scan_true_commits_relation.
  exact Hscan.
Qed.

Theorem phase1_surface_true_proposition_atom_derivation_commits_literal_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ELiteral "true") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    proposition_atom_decision input = Some (ChooseAlternative 2).
Proof.
  intros path input rest tree Hderive Hcontinuation.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules path "true" input rest tree Hderive)
    as [tail [Hinput [Hrest _]]].
  rewrite Hrest in Hcontinuation.
  rewrite Hinput.
  apply proposition_true_scan_false_commits_literal.
  eapply phase1_surface_proposition_atom_accepting_continuation_stops_relation_scan.
  exact Hcontinuation.
Qed.

Theorem phase1_surface_false_proposition_atom_derivation_commits_literal_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ELiteral "false") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    proposition_atom_decision input = Some (ChooseAlternative 3).
Proof.
  intros path input rest tree Hderive Hcontinuation.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules path "false" input rest tree Hderive)
    as [tail [Hinput [Hrest _]]].
  rewrite Hrest in Hcontinuation.
  rewrite Hinput.
  apply proposition_false_scan_false_commits_literal.
  eapply phase1_surface_proposition_atom_accepting_continuation_stops_relation_scan.
  exact Hcontinuation.
Qed.

Definition phase1_surface_grouped_proposition_expression : EbnfExpression :=
  ESequence
    [ ELiteral "("
    ; ENonterminal "proposition"
    ; ELiteral ")"
    ].

Theorem phase1_surface_grouped_proposition_atom_derivation_commits_grouping_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_grouped_proposition_expression input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    proposition_atom_decision input = Some (ChooseAlternative 1).
Proof.
  intros path input rest tree Hderive Hcontinuation.
  unfold phase1_surface_grouped_proposition_expression in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "("
      ; ENonterminal "proposition"
      ; ELiteral ")"
      ]
      input rest tree Hderive)
    as [trees [_ Hitems]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 0
      (ELiteral "(")
      [ENonterminal "proposition"; ELiteral ")"]
      input rest trees Hitems)
    as [after_open [open_tree [tail_trees [Hopen Htail]]]].
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 0))
      "(" input after_open open_tree Hopen)
    as [open_tail [Hinput [Hopen_rest _]]].
  assert (Hinput_open : input = TLiteral "(" :: after_open).
  {
    rewrite Hinput.
    rewrite Hopen_rest.
    reflexivity.
  }
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 1
      (ENonterminal "proposition")
      [ELiteral ")"]
      after_open rest tail_trees Htail)
    as [after_proposition
        [proposition_tree [close_trees [Hproposition Hclose_tail]]]].
  destruct
    (phase1_surface_nonterminal_derivation_is_delimiter_balanced
      (descend path (AtSequence 1))
      "proposition" after_open after_proposition
      proposition_tree Hproposition)
    as [consumed [Hproposition_input Hbalanced]].
  pose proof
    (delimiter_balanced_prefix_is_relation_neutral_positive
      consumed 0 Hbalanced)
    as Hneutral.
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules path 2
      (ELiteral ")") []
      after_proposition rest close_trees Hclose_tail)
    as [after_close [close_tree [nil_trees [Hclose Hnil]]]].
  pose proof
    (derives_sequence_nil_input_eq_rest
      phase1_surface_rules path 3
      after_close rest nil_trees Hnil)
    as Hafter_close.
  destruct
    (literal_derivation_is_exact
      phase1_surface_rules
      (descend path (AtSequence 2))
      ")" after_proposition after_close close_tree Hclose)
    as [close_tail [Hclose_input [Hclose_rest _]]].
  assert (Hclose_prefix :
    after_proposition = TLiteral ")" :: rest).
  {
    rewrite Hclose_input.
    rewrite <- Hclose_rest.
    rewrite Hafter_close.
    reflexivity.
  }
  pose proof
    (phase1_surface_proposition_atom_accepting_continuation_stops_relation_scan
      rest Hcontinuation)
    as Hrest_scan.
  assert (Hafter_open_scan : relation_commit_scan 1 after_open = false).
  {
    rewrite Hproposition_input.
    rewrite Hclose_prefix.
    rewrite
      (relation_commit_scan_after_neutral_prefix
        1 consumed 1 (TLiteral ")" :: rest) Hneutral).
    simpl.
    exact Hrest_scan.
  }
  rewrite Hinput_open.
  apply proposition_parenthesis_scan_false_commits_grouping.
  exact Hafter_open_scan.
Qed.

Lemma phase1_surface_claim_application_lookup_prefix :
  exists tail_items,
    lookupRule "claim_application" phase1_surface_rules =
      Some
        (ESequence
          (ENonterminal "static_reference" :: tail_items)).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Lemma phase1_surface_static_reference_lookup_for_claim :
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

Lemma phase1_surface_claim_application_derivation_starts_identifier :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "claim_application") input rest tree ->
    exists lexeme tail,
      input = TLexical "IDENTIFIER" lexeme :: tail.
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_claim_application_lookup_prefix
    as [claim_tail Hclaim_lookup].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "claim_application"
      input rest tree Hderive)
    as [claim_body [claim_tree [Hlookup [_ Hclaim_body]]]].
  rewrite Hclaim_lookup in Hlookup.
  inversion Hlookup; subst claim_body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "claim_application"))
      (ENonterminal "static_reference" :: claim_tail)
      input rest claim_tree Hclaim_body)
    as [claim_trees [_ Hclaim_items]].
  destruct
    (derives_sequence_cons_exposes_head
      phase1_surface_rules
      (descend path (AtNonterminal "claim_application")) 0
      (ENonterminal "static_reference") claim_tail
      input rest claim_trees Hclaim_items)
    as [after_static_reference
        [static_reference_tree [claim_tail_trees [Hstatic_reference _]]]].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules
      (descend
        (descend path (AtNonterminal "claim_application"))
        (AtSequence 0))
      "static_reference"
      input after_static_reference static_reference_tree Hstatic_reference)
    as [static_body [static_tree [Hstatic_lookup [_ Hstatic_body]]]].
  rewrite phase1_surface_static_reference_lookup_for_claim in Hstatic_lookup.
  inversion Hstatic_lookup; subst static_body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend
        (descend
          (descend path (AtNonterminal "claim_application"))
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
          (descend path (AtNonterminal "claim_application"))
          (AtSequence 0))
        (AtNonterminal "static_reference")) 0
      (ENonterminal "qualified_name")
      [EOptional (ENonterminal "static_arguments")]
      input after_static_reference static_trees Hstatic_items)
    as [after_qualified_name
        [qualified_tree [static_tail_trees [Hqualified _]]]].
  destruct
    (phase1_surface_qualified_name_derivation_is_exact
      (descend
        (descend
          (descend
            (descend path (AtNonterminal "claim_application"))
            (AtSequence 0))
          (AtNonterminal "static_reference"))
        (AtSequence 0))
      input after_qualified_name qualified_tree Hqualified)
    as [lexeme [more_names Hinput]].
  exists lexeme, (qualified_name_dot_tokens more_names after_qualified_name).
  exact Hinput.
Qed.

Theorem phase1_surface_claim_application_derivation_commits_claim_branch :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "claim_application") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    proposition_atom_decision input = Some (ChooseAlternative 4).
Proof.
  intros path input rest tree Hderive Hcontinuation.
  destruct
    (phase1_surface_claim_application_derivation_is_relation_neutral
      path input rest tree Hderive)
    as [consumed [Hinput_neutral Hneutral]].
  pose proof
    (phase1_surface_proposition_atom_accepting_continuation_stops_relation_scan
      rest Hcontinuation)
    as Hrest_scan.
  assert (Hscan : relation_commit_scan 0 input = false).
  {
    rewrite Hinput_neutral.
    rewrite
      (relation_commit_scan_after_neutral_prefix
        0 consumed 0 rest Hneutral).
    exact Hrest_scan.
  }
  destruct
    (phase1_surface_claim_application_derivation_starts_identifier
      path input rest tree Hderive)
    as [lexeme [tail Hinput]].
  rewrite Hinput in Hscan.
  simpl in Hscan.
  rewrite Hinput.
  apply proposition_identifier_scan_false_commits_claim.
  exact Hscan.
Qed.

Theorem phase1_surface_proposition_atom_nonrelation_structural_overlap_semantic_sound :
  (forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_grouped_proposition_expression input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    proposition_atom_decision input = Some (ChooseAlternative 1)) /\
  (forall path input rest tree,
    Derives phase1_surface_rules path
      (ELiteral "true") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    proposition_atom_decision input = Some (ChooseAlternative 2)) /\
  (forall path input rest tree,
    Derives phase1_surface_rules path
      (ELiteral "false") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    proposition_atom_decision input = Some (ChooseAlternative 3)) /\
  (forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "claim_application") input rest tree ->
    continuation_lookahead_mem
      rest phase1_surface_proposition_atom_follow = true ->
    proposition_atom_decision input = Some (ChooseAlternative 4)).
Proof.
  repeat split.
  - exact phase1_surface_grouped_proposition_atom_derivation_commits_grouping_branch.
  - exact phase1_surface_true_proposition_atom_derivation_commits_literal_branch.
  - exact phase1_surface_false_proposition_atom_derivation_commits_literal_branch.
  - exact phase1_surface_claim_application_derivation_commits_claim_branch.
Qed.
