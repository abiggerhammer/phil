From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyCertificate
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyWitnessSoundness
  GrammarDeterminacyContinuationSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Final-assembly coverage for PHIL-SURFACE-DETERM-001.

  The ordinary -> predictive-oracle conversion needs one small amount of
  information that the one-token FOLLOW certificate deliberately does not
  retain: at the five trailing-comma repetition sites, stopping on a comma is
  sound only when the next token is the enclosing close brace.  This checker
  records that exact local two-token shape while also classifying every other
  choice point as either a certified resolver root or a FIRST/FOLLOW-disjoint
  fallback site.

  Nonterminals remain reset boundaries, exactly as in the nullable/FIRST and
  FOLLOW coverage proofs.  The final mutual induction can therefore restart
  this checker from a successful lookupRule without unfolding callers.
*)

Definition token_intersection_emptyb
  (left right : list OverlapToken) : bool :=
  match token_intersection left right with
  | [] => true
  | _ => false
  end.

Definition expression_first_disjointb
  (left right : EbnfExpression) : bool :=
  token_intersection_emptyb
    (first_expression
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      left)
    (first_expression
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      right).

Fixpoint expression_first_disjoint_fromb
  (left : EbnfExpression)
  (rights : list EbnfExpression) : bool :=
  match rights with
  | [] => true
  | candidate :: rest =>
      andb
        (expression_first_disjointb left candidate)
        (expression_first_disjoint_fromb left rest)
  end.

Fixpoint alternatives_pairwise_first_disjointb
  (items : list EbnfExpression) : bool :=
  match items with
  | [] => true
  | item :: rest =>
      andb
        (expression_first_disjoint_fromb item rest)
        (alternatives_pairwise_first_disjointb rest)
  end.

Definition expression_follow_disjointb
  (expression : EbnfExpression)
  (outer_follow : list OverlapToken) : bool :=
  token_intersection_emptyb
    (first_expression
      phase1_surface_nullable_facts
      phase1_surface_first_facts
      expression)
    outer_follow.

Definition alternative_resolver_contextb
  (path : SyntaxPath)
  (outer_follow : list OverlapToken) : bool :=
  if path_has_suffixb path provider_declaration_suffix then true
  else if path_has_suffixb path generic_requirement_suffix then true
  else if path_has_suffixb path pattern_suffix then
    overlap_token_list_eqb
      outer_follow
      (lookup_tokens "pattern" phase1_surface_follow_facts)
  else if path_has_suffixb path primary_expression_suffix then true
  else if path_has_suffixb path proposition_atom_suffix then
    overlap_token_list_eqb
      outer_follow
      (lookup_tokens "proposition_atom" phase1_surface_follow_facts)
  else if path_has_suffixb path static_argument_suffix then true
  else false.

Definition comma_identifier_repetition_bodyb
  (body : EbnfExpression) : bool :=
  match body with
  | ESequence (ELiteral comma :: first :: _) =>
      andb (String.eqb comma ",")
        (andb
          (negb
            (nullable_expression
              phase1_surface_nullable_facts first))
          (andb
            (overlap_token_list_eqb
              (first_expression
                phase1_surface_nullable_facts
                phase1_surface_first_facts
                first)
              [OverlapLexicalClass "IDENTIFIER"])
            (choice_bodies_nonnullable_fuel expression_fuel first)))
  | _ => false
  end.

Definition trailing_comma_tail_shapeb
  (items : list EbnfExpression)
  (outer_follow : list OverlapToken) : bool :=
  match items with
  | [EOptional (ELiteral comma); ELiteral close] =>
      andb (String.eqb comma ",") (String.eqb close "}")
  | [EOptional (ELiteral comma)] =>
      andb
        (String.eqb comma ",")
        (overlap_token_list_eqb
          outer_follow [OverlapLiteral "}"])
  | _ => false
  end.

Definition sequence_head_assembly_guardb
  (path : SyntaxPath)
  (index : nat)
  (item : EbnfExpression)
  (rest : list EbnfExpression)
  (outer_follow : list OverlapToken) : bool :=
  match item with
  | ERepetition body =>
      if trailing_comma_repeat_pathb
           (descend path (AtSequence index))
      then
        andb
          (comma_identifier_repetition_bodyb body)
          (trailing_comma_tail_shapeb rest outer_follow)
      else true
  | _ => true
  end.

Definition repetition_assembly_guardb
  (path : SyntaxPath)
  (outer_follow : list OverlapToken)
  (body : EbnfExpression) : bool :=
  if trailing_comma_repeat_pathb path
  then comma_identifier_repetition_bodyb body
  else expression_follow_disjointb body outer_follow.

Definition oracle_assembly_fuel : nat := 512.

Fixpoint oracle_assembly_coverage_fuel
  (fuel : nat)
  (path : SyntaxPath)
  (outer_follow : list OverlapToken)
  (expression : EbnfExpression) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S remaining =>
      match expression with
      | ELiteral _ => true
      | ELexicalClass _ => true
      | ENonterminal _ => true
      | ESequence items =>
          oracle_assembly_sequence_coverage_fuel
            remaining path outer_follow 0 items
      | EAlternative items =>
          andb
            (orb
              (alternative_resolver_contextb path outer_follow)
              (alternatives_pairwise_first_disjointb items))
            (oracle_assembly_alternative_coverage_fuel
              remaining path outer_follow 0 items)
      | EOptional body =>
          andb
            (expression_follow_disjointb body outer_follow)
            (oracle_assembly_coverage_fuel
              remaining
              (descend path AtOptionalBody)
              outer_follow
              body)
      | ERepetition body =>
          andb
            (repetition_assembly_guardb path outer_follow body)
            (oracle_assembly_coverage_fuel
              remaining
              (descend path AtRepetitionBody)
              (phase1_surface_repetition_local_follow body outer_follow)
              body)
      end
  end

with oracle_assembly_sequence_coverage_fuel
  (fuel : nat)
  (path : SyntaxPath)
  (outer_follow : list OverlapToken)
  (index : nat)
  (items : list EbnfExpression) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S remaining =>
      match items with
      | [] => true
      | item :: rest =>
          let child_path := descend path (AtSequence index) in
          let child_follow :=
            phase1_surface_sequence_local_follow rest outer_follow in
          andb
            (sequence_head_assembly_guardb
              path index item rest outer_follow)
            (andb
              (oracle_assembly_coverage_fuel
                remaining child_path child_follow item)
              (oracle_assembly_sequence_coverage_fuel
                remaining path outer_follow (S index) rest))
      end
  end

with oracle_assembly_alternative_coverage_fuel
  (fuel : nat)
  (path : SyntaxPath)
  (outer_follow : list OverlapToken)
  (index : nat)
  (items : list EbnfExpression) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S remaining =>
      match items with
      | [] => true
      | item :: rest =>
          andb
            (oracle_assembly_coverage_fuel
              remaining
              (descend path (AtAlternative index))
              outer_follow
              item)
            (oracle_assembly_alternative_coverage_fuel
              remaining path outer_follow (S index) rest)
      end
  end.

Definition oracle_assembly_coverage_rule
  (rule : GrammarRule) : bool :=
  match rule with
  | (name, expression) =>
      oracle_assembly_coverage_fuel
        oracle_assembly_fuel
        [AtNonterminal name]
        (lookup_tokens name phase1_surface_follow_facts)
        expression
  end.

Theorem phase1_surface_all_rule_bodies_have_oracle_assembly_coverage :
  forallb oracle_assembly_coverage_rule phase1_surface_rules = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_rule_body_oracle_assembly_covered :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    oracle_assembly_coverage_fuel
      oracle_assembly_fuel
      [AtNonterminal name]
      (lookup_tokens name phase1_surface_follow_facts)
      body = true.
Proof.
  intros name body Hlookup.
  pose proof
    (lookupRule_forallb
      oracle_assembly_coverage_rule
      phase1_surface_rules
      name body
      phase1_surface_all_rule_bodies_have_oracle_assembly_coverage
      Hlookup) as Hcovered.
  exact Hcovered.
Qed.

Lemma oracle_assembly_sequence_cons_covered :
  forall fuel path outer_follow index item rest,
    oracle_assembly_sequence_coverage_fuel
      (S fuel) path outer_follow index (item :: rest) = true ->
    sequence_head_assembly_guardb
      path index item rest outer_follow = true /\
    oracle_assembly_coverage_fuel
      fuel
      (descend path (AtSequence index))
      (phase1_surface_sequence_local_follow rest outer_follow)
      item = true /\
    oracle_assembly_sequence_coverage_fuel
      fuel path outer_follow (S index) rest = true.
Proof.
  intros fuel path outer_follow index item rest Hcovered.
  simpl in Hcovered.
  apply andb_true_iff in Hcovered as [Hguard Hcovered].
  apply andb_true_iff in Hcovered as [Hitem Hrest].
  repeat split; assumption.
Qed.

Lemma oracle_assembly_alternative_member_covered :
  forall fuel path outer_follow base items relative item,
    oracle_assembly_alternative_coverage_fuel
      fuel path outer_follow base items = true ->
    nth_error items relative = Some item ->
    exists child_fuel,
      oracle_assembly_coverage_fuel
        child_fuel
        (descend path (AtAlternative (base + relative)))
        outer_follow
        item = true.
Proof.
  induction fuel as [| fuel IH];
    intros path outer_follow base items relative item Hcovered Hnth.
  - discriminate Hcovered.
  - destruct items as [| head rest]; simpl in Hnth; try discriminate.
    simpl in Hcovered.
    apply andb_true_iff in Hcovered as [Hhead Hrest].
    destruct relative as [| relative].
    + inversion Hnth; subst head.
      exists fuel.
      replace (base + 0) with base by lia.
      exact Hhead.
    + specialize
        (IH path outer_follow (S base) rest relative item Hrest Hnth)
        as [child_fuel Hchild].
      exists child_fuel.
      replace (base + S relative) with (S base + relative) by lia.
      exact Hchild.
Qed.

Lemma oracle_assembly_alternative_guard :
  forall fuel path outer_follow items,
    oracle_assembly_coverage_fuel
      (S fuel) path outer_follow (EAlternative items) = true ->
    orb
      (alternative_resolver_contextb path outer_follow)
      (alternatives_pairwise_first_disjointb items) = true.
Proof.
  intros fuel path outer_follow items Hcovered.
  simpl in Hcovered.
  apply andb_true_iff in Hcovered as [Hguard _].
  exact Hguard.
Qed.

Lemma oracle_assembly_optional_covered :
  forall fuel path outer_follow body,
    oracle_assembly_coverage_fuel
      (S fuel) path outer_follow (EOptional body) = true ->
    expression_follow_disjointb body outer_follow = true /\
    oracle_assembly_coverage_fuel
      fuel (descend path AtOptionalBody) outer_follow body = true.
Proof.
  intros fuel path outer_follow body Hcovered.
  simpl in Hcovered.
  apply andb_true_iff in Hcovered as [Hdisjoint Hbody].
  split; assumption.
Qed.

Lemma oracle_assembly_repetition_covered :
  forall fuel path outer_follow body,
    oracle_assembly_coverage_fuel
      (S fuel) path outer_follow (ERepetition body) = true ->
    repetition_assembly_guardb path outer_follow body = true /\
    oracle_assembly_coverage_fuel
      fuel
      (descend path AtRepetitionBody)
      (phase1_surface_repetition_local_follow body outer_follow)
      body = true.
Proof.
  intros fuel path outer_follow body Hcovered.
  simpl in Hcovered.
  apply andb_true_iff in Hcovered as [Hguard Hbody].
  split; assumption.
Qed.
