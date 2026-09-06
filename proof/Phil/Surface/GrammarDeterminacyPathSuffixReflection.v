From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolvers.

Import ListNotations.

Lemma syntax_path_step_eqb_eq :
  forall first second,
    syntax_path_step_eqb first second = true ->
    first = second.
Proof.
  intros first second Heq.
  destruct first as [first_name | first_index | first_index | |];
    destruct second as [second_name | second_index | second_index | |];
    simpl in Heq;
    try discriminate;
    try reflexivity.
  - apply String.eqb_eq in Heq.
    subst second_name.
    reflexivity.
  - apply Nat.eqb_eq in Heq.
    subst second_index.
    reflexivity.
  - apply Nat.eqb_eq in Heq.
    subst second_index.
    reflexivity.
Qed.

Lemma reversed_path_prefixb_true_shape :
  forall expected actual,
    reversed_path_prefixb expected actual = true ->
    exists rest,
      actual = expected ++ rest.
Proof.
  induction expected as [| expected_step expected_rest IH];
    intros actual Hprefix.
  - exists actual.
    reflexivity.
  - destruct actual as [| actual_step actual_rest].
    + discriminate Hprefix.
    + simpl in Hprefix.
      apply andb_true_iff in Hprefix as [Hstep Hrest].
      apply syntax_path_step_eqb_eq in Hstep.
      subst actual_step.
      destruct (IH actual_rest Hrest) as [rest Hshape].
      subst actual_rest.
      exists rest.
      reflexivity.
Qed.

Theorem path_has_suffixb_true_shape :
  forall path suffix,
    path_has_suffixb path suffix = true ->
    exists prefix,
      path = prefix ++ suffix.
Proof.
  intros path suffix Hsuffix.
  unfold path_has_suffixb in Hsuffix.
  destruct
    (reversed_path_prefixb_true_shape
      (rev suffix) (rev path) Hsuffix)
    as [rest Hshape].
  exists (rev rest).
  pose proof
    (f_equal (@rev SyntaxPathStep) Hshape)
    as Hrev.
  rewrite rev_involutive in Hrev.
  rewrite rev_app_distr in Hrev.
  rewrite rev_involutive in Hrev.
  exact Hrev.
Qed.
