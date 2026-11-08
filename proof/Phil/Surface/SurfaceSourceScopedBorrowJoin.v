From Stdlib Require Import Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.

(*
  FSEM-01: bounded source borrow scopes across a two-continuing-predecessor
  if join. The Haskell source bridge observes the ACTUAL production
  evalBorrowTraced and Context.joinContinuing operations; the following
  propositions are conditional facts about the Rocq ContextJoin model.
  They are not a universal parser / Map / Text / error correspondence proof.
*)

Definition BorrowLoanLive (ctx : Context.ResourceContext) (owner : Syntax.Name)
  : Prop := Context.sharedLoans ctx owner = true.

Definition BorrowLoanClosed (ctx : Context.ResourceContext) (owner : Syntax.Name)
  : Prop := Context.sharedLoans ctx owner = false.

(* An active loan on either continuing predecessor is inconsistent with
   the already-proved successful ContextJoin resource relation. *)
Theorem active_left_scoped_loan_blocks_continuing_join :
  forall left right joined owner,
    BorrowLoanLive left owner ->
    ~ ContextJoin.ContextJoinSuccess [left;right] joined.
Proof.
  intros left right joined owner Hlive Hjoin.
  pose proof
    (ContextJoin.context_join_inputs_have_no_loans
      [left;right] joined Hjoin) as Hinputs.
  apply Forall_forall with (x := left) in Hinputs.
  - unfold ContextJoin.NoLoans in Hinputs.
    unfold BorrowLoanLive in Hlive.
    specialize (Hinputs owner).
    rewrite Hlive in Hinputs.
    discriminate.
  - simpl. left. reflexivity.
Qed.

Theorem active_right_scoped_loan_blocks_continuing_join :
  forall left right joined owner,
    BorrowLoanLive right owner ->
    ~ ContextJoin.ContextJoinSuccess [left;right] joined.
Proof.
  intros left right joined owner Hlive Hjoin.
  pose proof
    (ContextJoin.context_join_inputs_have_no_loans
      [left;right] joined Hjoin) as Hinputs.
  apply Forall_forall with (x := right) in Hinputs.
  - unfold ContextJoin.NoLoans in Hinputs.
    unfold BorrowLoanLive in Hlive.
    specialize (Hinputs owner).
    rewrite Hlive in Hinputs.
    discriminate.
  - simpl. right. left. reflexivity.
Qed.

Theorem accepted_scoped_join_has_closed_loan :
  forall left right joined owner,
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    BorrowLoanClosed joined owner.
Proof.
  intros left right joined owner Hjoin.
  pose proof
    (ContextJoin.context_join_output_has_no_loans
      [left;right] joined Hjoin) as Hno.
  unfold BorrowLoanClosed, ContextJoin.NoLoans in *.
  apply Hno.
Qed.

Theorem accepted_scoped_join_requires_closed_predecessors :
  forall left right joined owner,
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    BorrowLoanClosed left owner /\ BorrowLoanClosed right owner.
Proof.
  intros left right joined owner Hjoin.
  pose proof
    (ContextJoin.context_join_inputs_have_no_loans
      [left;right] joined Hjoin) as Hinputs.
  split.
  - apply Forall_forall with (x := left) in Hinputs.
    + unfold BorrowLoanClosed, ContextJoin.NoLoans in *.
      apply Hinputs.
    + simpl. left. reflexivity.
  - apply Forall_forall with (x := right) in Hinputs.
    + unfold BorrowLoanClosed, ContextJoin.NoLoans in *.
      apply Hinputs.
    + simpl. right. left. reflexivity.
Qed.

(* A source borrow whose observed result is a BorrowEscape rejection cannot
   invent an after-branch continuation; this is a bounded MODEL interface.
   Actual Haskell source error classifications and trace prefix fidelity
   remain separately enforced by the source conformance tests. *)
Inductive SourceBorrowResult : Type :=
| BorrowClosedSuccessfully
| BorrowEscapedAndRejected.

Definition projectedContinuingBorrow
    (outcome : SourceBorrowResult) (context : Context.ResourceContext)
  : option Context.ResourceContext :=
  match outcome with
  | BorrowClosedSuccessfully => Some context
  | BorrowEscapedAndRejected => None
  end.

Theorem rejected_source_borrow_has_no_continuing_predecessor :
  forall context,
    projectedContinuingBorrow BorrowEscapedAndRejected context = None.
Proof. intros; reflexivity. Qed.

Theorem successful_source_borrow_retains_its_exact_predecessor :
  forall context,
    projectedContinuingBorrow BorrowClosedSuccessfully context = Some context.
Proof. intros; reflexivity. Qed.

Print Assumptions active_left_scoped_loan_blocks_continuing_join.
Print Assumptions active_right_scoped_loan_blocks_continuing_join.
Print Assumptions accepted_scoped_join_has_closed_loan.
Print Assumptions accepted_scoped_join_requires_closed_predecessors.
Print Assumptions rejected_source_borrow_has_no_continuing_predecessor.
Print Assumptions successful_source_borrow_retains_its_exact_predecessor.
