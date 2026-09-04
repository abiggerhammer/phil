From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyWitnessSoundness
  GrammarDeterminacyContinuationSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  FOLLOW-coverage foundation for the final PHIL-SURFACE-DETERM-001 bridge.

  The continuation-sensitive structural resolvers use the computed global
  FOLLOW set of their enclosing nonterminal.  During the final mutual
  derivation induction, however, sequence/optional/repetition structure carries
  a smaller local continuation set.  This file certifies mechanically that
  every generated Grammar-v1 nonterminal occurrence receives a local FOLLOW
  set contained in that nonterminal's computed global FOLLOW set.

  The checker mirrors exactly the local FOLLOW propagation used by
  GrammarDeterminacyFollowOverlap.v and GrammarDeterminacyContinuationSoundness.v.
  It stops at nonterminals, where the fixed-point table is the proof boundary;
  entering the referenced rule resets traversal fuel and uses that rule's
  separately certified body coverage.
*)

Definition token_subsetb
  (left right : list OverlapToken) : bool :=
  forallb (fun token => token_mem token right) left.

Lemma follow_token_mem_true_in :
  forall token tokens,
    token_mem token tokens = true ->
    In token tokens.
Proof.
  intros token tokens.
  induction tokens as [| head tail IH]; intros Hmem.
  - discriminate Hmem.
  - simpl in Hmem.
    destruct (overlap_token_eqb token head) eqn:Heq.
    + apply overlap_token_eqb_eq in Heq.
      subst head.
      left. reflexivity.
    + right.
      apply IH.
      exact Hmem.
Qed.

Lemma token_subsetb_member :
  forall token left right,
    token_subsetb left right = true ->
    token_mem token left = true ->
    token_mem token right = true.
Proof.
  intros token left right Hsubset Hmember.
  unfold token_subsetb in Hsubset.
  rewrite forallb_forall in Hsubset.
  apply follow_token_mem_true_in in Hmember.
  exact (Hsubset token Hmember).
Qed.

Lemma continuation_lookahead_mem_subset :
  forall input left right,
    token_subsetb left right = true ->
    continuation_lookahead_mem input left = true ->
    continuation_lookahead_mem input right = true.
Proof.
  intros input left right Hsubset Hcontinuation.
  destruct input as [| first_token rest];
    unfold continuation_lookahead_mem in *.
  - eapply token_subsetb_member; eauto.
  - eapply token_subsetb_member; eauto.
Qed.

Fixpoint follow_coverage_fuel
  (fuel : nat)
  (outer_follow : list OverlapToken)
  (expression : EbnfExpression) : bool :=
  match fuel with
  | O => false
  | S remaining =>
      match expression with
      | ELiteral _ => true
      | ELexicalClass _ => true
      | ENonterminal name =>
          token_subsetb
            outer_follow
            (lookup_tokens name phase1_surface_follow_facts)
      | ESequence items =>
          let fix cover_sequence
            (pending : list EbnfExpression) : bool :=
            match pending with
            | [] => true
            | item :: rest =>
                andb
                  (follow_coverage_fuel
                    remaining
                    (phase1_surface_sequence_local_follow rest outer_follow)
                    item)
                  (cover_sequence rest)
            end
          in cover_sequence items
      | EAlternative items =>
          forallb
            (follow_coverage_fuel remaining outer_follow)
            items
      | EOptional body =>
          follow_coverage_fuel remaining outer_follow body
      | ERepetition body =>
          follow_coverage_fuel
            remaining
            (phase1_surface_repetition_local_follow body outer_follow)
            body
      end
  end.

Definition follow_coverage_rule (rule : GrammarRule) : bool :=
  match rule with
  | (name, body) =>
      follow_coverage_fuel
        expression_fuel
        (lookup_tokens name phase1_surface_follow_facts)
        body
  end.

Theorem phase1_surface_all_rule_bodies_have_follow_coverage :
  forallb follow_coverage_rule phase1_surface_rules = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma follow_coverage_rule_pair :
  forall name body,
    follow_coverage_rule (name, body) =
    follow_coverage_fuel
      expression_fuel
      (lookup_tokens name phase1_surface_follow_facts)
      body.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_rule_body_follow_covered :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    follow_coverage_fuel
      expression_fuel
      (lookup_tokens name phase1_surface_follow_facts)
      body = true.
Proof.
  intros name body Hlookup.
  assert (Hcovered : follow_coverage_rule (name, body) = true).
  {
    eapply lookupRule_forallb.
    - exact phase1_surface_all_rule_bodies_have_follow_coverage.
    - exact Hlookup.
  }
  rewrite follow_coverage_rule_pair in Hcovered.
  exact Hcovered.
Qed.

Lemma follow_coverage_nonterminal_equation :
  forall fuel outer_follow name,
    follow_coverage_fuel
      (S fuel) outer_follow (ENonterminal name) =
    token_subsetb
      outer_follow
      (lookup_tokens name phase1_surface_follow_facts).
Proof.
  reflexivity.
Qed.

Lemma follow_coverage_sequence_cons_equation :
  forall fuel outer_follow item items,
    follow_coverage_fuel
      (S fuel) outer_follow (ESequence (item :: items)) =
    andb
      (follow_coverage_fuel
        fuel
        (phase1_surface_sequence_local_follow items outer_follow)
        item)
      (follow_coverage_fuel
        (S fuel) outer_follow (ESequence items)).
Proof.
  reflexivity.
Qed.

Lemma follow_coverage_alternative_equation :
  forall fuel outer_follow items,
    follow_coverage_fuel
      (S fuel) outer_follow (EAlternative items) =
    forallb (follow_coverage_fuel fuel outer_follow) items.
Proof.
  reflexivity.
Qed.

Lemma follow_coverage_optional_equation :
  forall fuel outer_follow body,
    follow_coverage_fuel
      (S fuel) outer_follow (EOptional body) =
    follow_coverage_fuel fuel outer_follow body.
Proof.
  reflexivity.
Qed.

Lemma follow_coverage_repetition_equation :
  forall fuel outer_follow body,
    follow_coverage_fuel
      (S fuel) outer_follow (ERepetition body) =
    follow_coverage_fuel
      fuel
      (phase1_surface_repetition_local_follow body outer_follow)
      body.
Proof.
  reflexivity.
Qed.

Lemma follow_coverage_nonterminal_subset :
  forall fuel outer_follow name,
    follow_coverage_fuel
      (S fuel) outer_follow (ENonterminal name) = true ->
    token_subsetb
      outer_follow
      (lookup_tokens name phase1_surface_follow_facts) = true.
Proof.
  intros fuel outer_follow name Hcovered.
  rewrite follow_coverage_nonterminal_equation in Hcovered.
  exact Hcovered.
Qed.

Theorem follow_coverage_lifts_nonterminal_continuation :
  forall fuel outer_follow name input,
    follow_coverage_fuel
      (S fuel) outer_follow (ENonterminal name) = true ->
    continuation_lookahead_mem input outer_follow = true ->
    continuation_lookahead_mem
      input
      (lookup_tokens name phase1_surface_follow_facts) = true.
Proof.
  intros fuel outer_follow name input Hcovered Hcontinuation.
  eapply continuation_lookahead_mem_subset.
  - eapply follow_coverage_nonterminal_subset.
    exact Hcovered.
  - exact Hcontinuation.
Qed.

Lemma follow_coverage_sequence_head :
  forall fuel outer_follow item items,
    follow_coverage_fuel
      (S fuel) outer_follow (ESequence (item :: items)) = true ->
    follow_coverage_fuel
      fuel
      (phase1_surface_sequence_local_follow items outer_follow)
      item = true.
Proof.
  intros fuel outer_follow item items Hcovered.
  rewrite follow_coverage_sequence_cons_equation in Hcovered.
  apply andb_true_iff in Hcovered as [Hhead _].
  exact Hhead.
Qed.

Lemma follow_coverage_sequence_tail :
  forall fuel outer_follow item items,
    follow_coverage_fuel
      (S fuel) outer_follow (ESequence (item :: items)) = true ->
    follow_coverage_fuel
      (S fuel) outer_follow (ESequence items) = true.
Proof.
  intros fuel outer_follow item items Hcovered.
  rewrite follow_coverage_sequence_cons_equation in Hcovered.
  apply andb_true_iff in Hcovered as [_ Htail].
  exact Htail.
Qed.

Lemma follow_coverage_alternative_member :
  forall fuel outer_follow items index item,
    follow_coverage_fuel
      (S fuel) outer_follow (EAlternative items) = true ->
    nth_error items index = Some item ->
    follow_coverage_fuel fuel outer_follow item = true.
Proof.
  intros fuel outer_follow items index item Hcovered Hnth.
  rewrite follow_coverage_alternative_equation in Hcovered.
  rewrite forallb_forall in Hcovered.
  apply Hcovered.
  eapply nth_error_In.
  exact Hnth.
Qed.

Lemma follow_coverage_optional_body :
  forall fuel outer_follow body,
    follow_coverage_fuel
      (S fuel) outer_follow (EOptional body) = true ->
    follow_coverage_fuel fuel outer_follow body = true.
Proof.
  intros fuel outer_follow body Hcovered.
  rewrite follow_coverage_optional_equation in Hcovered.
  exact Hcovered.
Qed.

Lemma follow_coverage_repetition_body :
  forall fuel outer_follow body,
    follow_coverage_fuel
      (S fuel) outer_follow (ERepetition body) = true ->
    follow_coverage_fuel
      fuel
      (phase1_surface_repetition_local_follow body outer_follow)
      body = true.
Proof.
  intros fuel outer_follow body Hcovered.
  rewrite follow_coverage_repetition_equation in Hcovered.
  exact Hcovered.
Qed.

Definition phase1_surface_start_follow : list OverlapToken :=
  lookup_tokens phase1_surface_start phase1_surface_follow_facts.

Theorem phase1_surface_start_follow_accepts_eof :
  continuation_lookahead_mem [] phase1_surface_start_follow = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_root_follow_covered :
  follow_coverage_fuel
    expression_fuel
    phase1_surface_start_follow
    (ENonterminal phase1_surface_start) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.
