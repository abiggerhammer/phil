From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.
From Phil.Surface Require Import SurfaceSourceLinearLoopTransfer.

(*
  FSEM-01 L-3: normalized one-owner loan lifecycle inside a statically
  source-checked Linear Bytes loop body. The actual Haskell production loan,
  consumption and join operations are separately exercised by source fixtures.
  This is not a source-to-Rocq or native implementation refinement theorem.
*)

Definition modeledLoanSet (owner : Syntax.Name) (live : bool)
    (ctx : Context.ResourceContext) : Context.LoanSet :=
  fun candidate =>
    if String.eqb candidate owner then live
    else Context.sharedLoans ctx candidate.

Definition withModeledLoan (owner : Syntax.Name) (live : bool)
    (ctx : Context.ResourceContext) : Context.ResourceContext :=
  Context.mkResourceContext
    (Context.unrestrictedBindings ctx)
    (Context.affineBindings ctx)
    (Context.linearBindings ctx)
    (modeledLoanSet owner live ctx).

Theorem scoped_loop_loan_opens_at_exact_owner :
  forall header owner,
    Context.sharedLoans (withModeledLoan owner true header) owner = true.
Proof.
  intros. unfold withModeledLoan, modeledLoanSet. simpl.
  now rewrite String.eqb_refl.
Qed.

Theorem scoped_loop_loan_closes_at_exact_owner :
  forall header owner,
    Context.sharedLoans (withModeledLoan owner false header) owner = false.
Proof.
  intros. unfold withModeledLoan, modeledLoanSet. simpl.
  now rewrite String.eqb_refl.
Qed.

Theorem scoped_loop_loan_changes_no_resource_binding_map :
  forall header owner live candidate,
    Context.unrestrictedBindings (withModeledLoan owner live header) candidate =
      Context.unrestrictedBindings header candidate /\
    Context.affineBindings (withModeledLoan owner live header) candidate =
      Context.affineBindings header candidate /\
    Context.linearBindings (withModeledLoan owner live header) candidate =
      Context.linearBindings header candidate.
Proof.
  intros. repeat split; reflexivity.
Qed.

Theorem closed_scoped_loop_loan_restores_original_loan_observations :
  forall header owner candidate,
    Context.sharedLoans header owner = false ->
    Context.sharedLoans
      (withModeledLoan owner false (withModeledLoan owner true header))
      candidate = Context.sharedLoans header candidate.
Proof.
  intros header owner candidate Hclosed.
  unfold withModeledLoan, modeledLoanSet. simpl.
  destruct (String.eqb candidate owner) eqn:Heq.
  - apply String.eqb_eq in Heq. subst candidate. exact (eq_sym Hclosed).
  - reflexivity.
Qed.

Theorem active_scoped_loop_loan_blocks_linear_continue_move :
  forall header owner,
    Context.sharedLoans header owner = true ->
    Context.consumeLinear owner header =
      Context.ConsumeError (Context.OwnerBorrowed owner).
Proof.
  intros header owner Hloan.
  unfold Context.consumeLinear.
  now rewrite Hloan.
Qed.

Theorem successful_linear_continue_requires_closed_owner_loan :
  forall header spent owner ty,
    Context.consumeLinear owner header = Context.Consumed ty spent ->
    Context.sharedLoans header owner = false.
Proof.
  intros header spent owner ty Hconsume.
  unfold Context.consumeLinear in Hconsume.
  destruct (Context.sharedLoans header owner) eqn:Hloan.
  - discriminate.
  - reflexivity.
Qed.

Theorem unclosed_scoped_loop_loan_refuses_continuing_reentry :
  forall header rebound joined owner,
    Context.sharedLoans rebound owner = true ->
    ~ ContextJoin.ContextJoinSuccess [header; rebound] joined.
Proof.
  intros header rebound joined owner Hlive Hjoin.
  pose proof (ContextJoin.context_join_inputs_have_no_loans
    [header;rebound] joined Hjoin) as Hinputs.
  apply Forall_forall with (x := rebound) in Hinputs.
  - unfold ContextJoin.NoLoans in Hinputs.
    specialize (Hinputs owner).
    rewrite Hlive in Hinputs. discriminate.
  - simpl. right. left. reflexivity.
Qed.

Theorem closed_scoped_loop_loan_backedge_preserves_header_owner :
  forall header spent rebound joined owner ty,
    Context.consumeLinear owner header = Context.Consumed ty spent ->
    Context.insertBinding Syntax.Linear owner ty spent =
      Context.Inserted rebound ->
    ContextJoin.ContextJoinSuccess [header;rebound] joined ->
    Context.linearBindings joined owner = Some ty /\
    ContextJoin.NoLoans joined.
Proof.
  intros header spent rebound joined owner ty Hconsume Hinsert Hjoin.
  pose proof (linear_loop_backedge_consumes_then_rebinds_exact_header
    header spent rebound owner ty Hconsume Hinsert)
    as [Hheader _].
  split.
  - exact (linear_loop_reentry_has_exact_linear_header
      header rebound joined owner ty Hheader Hjoin).
  - exact (ContextJoin.context_join_output_has_no_loans
      [header;rebound] joined Hjoin).
Qed.

Print Assumptions scoped_loop_loan_opens_at_exact_owner.
Print Assumptions scoped_loop_loan_closes_at_exact_owner.
Print Assumptions scoped_loop_loan_changes_no_resource_binding_map.
Print Assumptions closed_scoped_loop_loan_restores_original_loan_observations.
Print Assumptions active_scoped_loop_loan_blocks_linear_continue_move.
Print Assumptions successful_linear_continue_requires_closed_owner_loan.
Print Assumptions unclosed_scoped_loop_loan_refuses_continuing_reentry.
Print Assumptions closed_scoped_loop_loan_backedge_preserves_header_owner.
