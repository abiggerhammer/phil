From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.
From Phil.Surface Require Import
  SurfaceSourceScopedBorrowJoin SurfaceSourceLinearLoopTransfer.

(*
  FSEM-01 CORR-2: compose the *bounded conditional* source-join and
  one-slot Linear loop transition models over the same resource context.
  The accompanying Haskell source tests independently reconstruct actual
  Core cuts and reject forged error prefixes. No native Haskell<->Rocq
  refinement, operational iteration, or full source semantics is claimed.
*)

Theorem corr2_join_preserves_linear_and_closes_all_loan_cuts :
  forall (left right joined : Context.ResourceContext)
         (owner : Syntax.Name) (ty : Syntax.Ty),
    ContextJoin.ContextJoinSuccess [left;right] joined ->
    Context.linearBindings left owner = Some ty ->
    Context.linearBindings joined owner = Some ty /\
    SurfaceSourceScopedBorrowJoin.BorrowLoanClosed left owner /\
    SurfaceSourceScopedBorrowJoin.BorrowLoanClosed right owner /\
    SurfaceSourceScopedBorrowJoin.BorrowLoanClosed joined owner.
Proof.
  intros left right joined owner ty Hjoin Hlinear.
  pose proof (ContextJoin.context_join_linear_converges
    [left;right] joined left Hjoin (or_introl eq_refl))
    as Hsame.
  unfold ContextJoin.SameBindingMap in Hsame.
  pose proof
    (SurfaceSourceScopedBorrowJoin.accepted_scoped_join_requires_closed_predecessors
      left right joined owner Hjoin) as [Hleft Hright].
  pose proof
    (SurfaceSourceScopedBorrowJoin.accepted_scoped_join_has_closed_loan
      left right joined owner Hjoin) as Hclosed.
  repeat split.
  - rewrite Hsame. exact Hlinear.
  - exact Hleft.
  - exact Hright.
  - exact Hclosed.
Qed.

Theorem corr2_loop_entry_backedge_and_join_preserve_exact_owner :
  forall (initial spent header backSpent rebound joined : Context.ResourceContext)
         (old slot : Syntax.Name) (ty : Syntax.Ty),
    Context.consumeLinear old initial = Context.Consumed ty spent ->
    Context.insertBinding Syntax.Linear slot ty spent =
      Context.Inserted header ->
    Context.consumeLinear slot header = Context.Consumed ty backSpent ->
    Context.insertBinding Syntax.Linear slot ty backSpent =
      Context.Inserted rebound ->
    String.eqb old slot = false ->
    ContextJoin.ContextJoinSuccess [header;rebound] joined ->
    Context.linearBindings joined old = None /\
    Context.linearBindings joined slot = Some ty /\
    ContextJoin.NoLoans joined /\
    Context.insertBinding Syntax.Linear slot ty header =
      Context.InsertError (Context.DuplicateBinding slot).
Proof.
  intros initial spent header backSpent rebound joined old slot ty
    Hentry Hheader Hback Hrebound Hdistinct Hjoin.
  pose proof
    (SurfaceSourceLinearLoopTransfer.linear_loop_entry_consumes_old_owner_and_installs_header
      initial spent header old slot ty Hentry Hheader)
    as [_ [_ Hslot]].
  pose proof
    (SurfaceSourceLinearLoopTransfer.linear_loop_moved_old_owner_does_not_reappear
      initial spent header old slot ty Hentry Hheader Hdistinct)
    as Hold.
  pose proof
    (SurfaceSourceLinearLoopTransfer.linear_loop_reentry_preserves_every_linear_owner
      header rebound joined old Hjoin)
    as [HjoinedOld _].
  pose proof
    (SurfaceSourceLinearLoopTransfer.linear_loop_reentry_has_exact_linear_header
      header rebound joined slot ty Hslot Hjoin)
    as HjoinedSlot.
  pose proof
    (SurfaceSourceLinearLoopTransfer.linear_loop_reentry_closes_all_loans
      header rebound joined Hjoin)
    as Hclosed.
  pose proof
    (SurfaceSourceLinearLoopTransfer.linear_loop_duplicate_live_header_is_rejected
      header slot ty Hslot)
    as Hduplicate.
  repeat split.
  - rewrite HjoinedOld. exact Hold.
  - exact HjoinedSlot.
  - exact Hclosed.
  - exact Hduplicate.
Qed.

Theorem corr2_live_loan_cannot_cross_two_predecessor_reentry :
  forall (header rebound joined : Context.ResourceContext)
         (owner : Syntax.Name),
    Context.sharedLoans rebound owner = true ->
    ~ ContextJoin.ContextJoinSuccess [header;rebound] joined.
Proof.
  intros header rebound joined owner Hactive.
  apply
    (SurfaceSourceScopedBorrowJoin.active_right_scoped_loan_blocks_continuing_join
      header rebound joined owner).
  exact Hactive.
Qed.

Print Assumptions corr2_join_preserves_linear_and_closes_all_loan_cuts.
Print Assumptions corr2_loop_entry_backedge_and_join_preserve_exact_owner.
Print Assumptions corr2_live_loan_cannot_cross_two_predecessor_reentry.
