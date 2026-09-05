From Stdlib Require Import Bool.Bool Lists.List Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacySimpleResolvers
  GrammarDeterminacyWitnessSoundness
  GrammarDeterminacyOracleAssemblyCoverage.

Import ListNotations.

(*
  Propositional reflection for the mechanically checked oracle-assembly
  coverage introduced by #723.  The final ordinary-derivation -> predictive-
  oracle conversion should consume small logical facts, not unfold boolean
  checkers or their fuelled traversals.
*)

Lemma assembly_overlap_token_list_eqb_eq :
  forall left right,
    overlap_token_list_eqb left right = true ->
    left = right.
Proof.
  induction left as [| head rest IH]; intros right Heq;
    destruct right as [| candidate tail]; simpl in Heq; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Heq as [Hhead Htail].
    apply overlap_token_eqb_eq in Hhead.
    subst candidate.
    f_equal.
    apply IH.
    exact Htail.
Qed.

Lemma token_intersection_emptyb_sound :
  forall left right,
    token_intersection_emptyb left right = true ->
    token_intersection left right = [].
Proof.
  intros left right Hempty.
  unfold token_intersection_emptyb in Hempty.
  destruct (token_intersection left right) as [| head rest] eqn:Hintersection.
  - reflexivity.
  - discriminate Hempty.
Qed.

Lemma expression_first_disjointb_equation :
  forall left right,
    expression_first_disjointb left right =
    token_intersection_emptyb
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        left)
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        right).
Proof.
  reflexivity.
Qed.

Lemma expression_first_disjointb_sound :
  forall left right,
    expression_first_disjointb left right = true ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        left)
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        right) = [].
Proof.
  intros left right Hdisjoint.
  rewrite expression_first_disjointb_equation in Hdisjoint.
  apply token_intersection_emptyb_sound in Hdisjoint.
  exact Hdisjoint.
Qed.

Lemma expression_follow_disjointb_equation :
  forall expression outer_follow,
    expression_follow_disjointb expression outer_follow =
    token_intersection_emptyb
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression)
      outer_follow.
Proof.
  reflexivity.
Qed.

Lemma expression_follow_disjointb_sound :
  forall expression outer_follow,
    expression_follow_disjointb expression outer_follow = true ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        expression)
      outer_follow = [].
Proof.
  intros expression outer_follow Hdisjoint.
  rewrite expression_follow_disjointb_equation in Hdisjoint.
  apply token_intersection_emptyb_sound in Hdisjoint.
  exact Hdisjoint.
Qed.

Lemma expression_first_disjoint_fromb_nth :
  forall left rights index right,
    expression_first_disjoint_fromb left rights = true ->
    nth_error rights index = Some right ->
    expression_first_disjointb left right = true.
Proof.
  intros left rights.
  induction rights as [| head rest IH];
    intros index right Hdisjoint Hnth.
  - destruct index; simpl in Hnth; discriminate.
  - change
      (andb
        (expression_first_disjointb left head)
        (expression_first_disjoint_fromb left rest) = true)
      in Hdisjoint.
    apply andb_true_iff in Hdisjoint as [Hhead Hrest].
    destruct index as [| index].
    + simpl in Hnth.
      inversion Hnth; subst head.
      exact Hhead.
    + simpl in Hnth.
      eapply IH.
      * exact Hrest.
      * exact Hnth.
Qed.

Lemma alternatives_pairwise_first_disjointb_nth_lt :
  forall items first_index first second_index second,
    alternatives_pairwise_first_disjointb items = true ->
    nth_error items first_index = Some first ->
    nth_error items second_index = Some second ->
    first_index < second_index ->
    expression_first_disjointb first second = true.
Proof.
  induction items as [| head rest IH];
    intros first_index first second_index second
      Hpairwise Hfirst Hsecond Hlt.
  - destruct first_index; simpl in Hfirst; discriminate.
  - change
      (andb
        (expression_first_disjoint_fromb head rest)
        (alternatives_pairwise_first_disjointb rest) = true)
      in Hpairwise.
    apply andb_true_iff in Hpairwise as [Hhead Hrest].
    destruct first_index as [| first_index].
    + simpl in Hfirst.
      inversion Hfirst; subst head.
      destruct second_index as [| second_index].
      * lia.
      * simpl in Hsecond.
        eapply expression_first_disjoint_fromb_nth.
        -- exact Hhead.
        -- exact Hsecond.
    + destruct second_index as [| second_index].
      * lia.
      * simpl in Hfirst, Hsecond.
        eapply IH.
        -- exact Hrest.
        -- exact Hfirst.
        -- exact Hsecond.
        -- lia.
Qed.

Lemma alternatives_pairwise_first_disjointb_nth_lt_sound :
  forall items first_index first second_index second,
    alternatives_pairwise_first_disjointb items = true ->
    nth_error items first_index = Some first ->
    nth_error items second_index = Some second ->
    first_index < second_index ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        first)
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        second) = [].
Proof.
  intros items first_index first second_index second
    Hpairwise Hfirst Hsecond Hlt.
  apply expression_first_disjointb_sound.
  eapply alternatives_pairwise_first_disjointb_nth_lt.
  - exact Hpairwise.
  - exact Hfirst.
  - exact Hsecond.
  - exact Hlt.
Qed.

Lemma sequence_head_assembly_guard_trailing :
  forall path index body rest outer_follow,
    trailing_comma_repeat_pathb
      (descend path (AtSequence index)) = true ->
    sequence_head_assembly_guardb
      path index (ERepetition body) rest outer_follow = true ->
    comma_identifier_repetition_bodyb body = true /\
    trailing_comma_tail_shapeb rest outer_follow = true.
Proof.
  intros path index body rest outer_follow Htrailing Hguard.
  unfold sequence_head_assembly_guardb in Hguard.
  rewrite Htrailing in Hguard.
  apply andb_true_iff in Hguard as [Hbody Htail].
  split; assumption.
Qed.

Lemma repetition_assembly_guard_trailing :
  forall path outer_follow body,
    trailing_comma_repeat_pathb path = true ->
    repetition_assembly_guardb path outer_follow body = true ->
    comma_identifier_repetition_bodyb body = true.
Proof.
  intros path outer_follow body Htrailing Hguard.
  unfold repetition_assembly_guardb in Hguard.
  rewrite Htrailing in Hguard.
  exact Hguard.
Qed.

Lemma repetition_assembly_guard_fallback :
  forall path outer_follow body,
    trailing_comma_repeat_pathb path = false ->
    repetition_assembly_guardb path outer_follow body = true ->
    expression_follow_disjointb body outer_follow = true.
Proof.
  intros path outer_follow body Htrailing Hguard.
  unfold repetition_assembly_guardb in Hguard.
  rewrite Htrailing in Hguard.
  exact Hguard.
Qed.
