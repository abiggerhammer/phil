From Stdlib Require Import Strings.String Bool.Bool Lists.List.
Import ListNotations.
From Phil.Core Require Import Syntax Context GenericStructural CallableMode CallableScope.

(* FSEM-01 CORR-1: conditional normalized stage/cut model.
   Source Grammar-v1 binder resolution, native Haskell Text/Map/Set
   observations, and producer fidelity are independently tested premises,
   NOT an arbitrary-Haskell-to-Rocq refinement theorem. *)

Definition modeledCaptureMove
  (owner : Syntax.Name) (before : Context.ResourceContext)
  : option Context.ResourceContext :=
  match Context.consumeLinear owner before with
  | Context.Consumed _ after => Some after
  | Context.ConsumeError _ => None
  end.

Definition modeledCaptureAfterPrecheck
  (first second : CallableMode.ClosureCapture)
  (owner : Syntax.Name) (before : Context.ResourceContext)
  : option Context.ResourceContext :=
  if CallableMode.duplicateCaptureAllowed first second
  then modeledCaptureMove owner before
  else None.

Theorem exact_native_capture_cut_and_frame :
  forall owner before after,
    modeledCaptureMove owner before = Some after ->
    exists ty,
      Context.linearBindings before owner = Some ty /\
      Context.linearBindings after owner = None /\
      (forall other,
         String.eqb other owner = false ->
         Context.linearBindings after other =
           Context.linearBindings before other) /\
      Context.unrestrictedBindings after =
        Context.unrestrictedBindings before /\
      Context.affineBindings after =
        Context.affineBindings before /\
      Context.sharedLoans after = Context.sharedLoans before.
Proof.
  intros owner before after Hstep.
  unfold modeledCaptureMove in Hstep.
  destruct (Context.consumeLinear owner before)
    as [err|ty result] eqn:Hnative; try discriminate.
  inversion Hstep; subst result; clear Hstep.
  exists ty.
  exact (Context.consumeLinear_success_exact owner before after ty Hnative).
Qed.

Theorem native_capture_error_has_no_successor :
  forall owner before err,
    Context.consumeLinear owner before = Context.ConsumeError err ->
    modeledCaptureMove owner before = None.
Proof.
  intros owner before err Herror.
  unfold modeledCaptureMove.
  now rewrite Herror.
Qed.

Theorem duplicate_linear_source_capture_blocks_move_before_native_use :
  forall occurrence first second owner before,
    modeledCaptureAfterPrecheck
      (CallableMode.mkClosureCapture occurrence first GenericStructural.Linear)
      (CallableMode.mkClosureCapture occurrence second GenericStructural.Linear)
      owner before = None.
Proof.
  intros.
  unfold modeledCaptureAfterPrecheck.
  now rewrite CallableMode.duplicate_linear_occurrence_is_rejected.
Qed.

Theorem active_scoped_loan_refuses_owner_move_without_successor :
  forall owner before,
    Context.sharedLoans before owner = true ->
    modeledCaptureMove owner before = None.
Proof.
  intros owner before Hloan.
  apply native_capture_error_has_no_successor with
    (err := Context.OwnerBorrowed owner).
  unfold Context.consumeLinear.
  now rewrite Hloan.
Qed.

Theorem successful_native_capture_reuse_fails_exactly :
  forall owner before after ty,
    Context.consumeLinear owner before = Context.Consumed ty after ->
    Context.consumeLinear owner after =
      Context.ConsumeError (Context.UnknownLinearBinding owner).
Proof.
  intros owner before after ty Hconsume.
  pose proof
    (Context.consumeLinear_success_exact owner before after ty Hconsume)
    as [_ [Hgone [_ [_ [_ Hloans]]]]].
  unfold Context.consumeLinear in Hconsume.
  destruct (Context.sharedLoans before owner) eqn:Hloan; try discriminate.
  unfold Context.consumeLinear.
  rewrite Hloans, Hloan, Hgone.
  reflexivity.
Qed.

(* An accepted source-local capture is conditionally scoped by an exact loan
   key. An escaping source capture cannot be promoted to a loan-close cut. *)
Definition modeledScopedClosureAccepted
  (extent : CallableScope.ClosureExtent)
  (capture : CallableScope.ClosureScopeCapture) : bool :=
  match CallableScope.decideClosureScopeCapture extent capture with
  | CallableScope.ScopeCaptureAccepted => true
  | _ => false
  end.

Theorem escaping_source_scoped_capture_has_no_accepted_close :
  forall captured loan,
    modeledScopedClosureAccepted
      CallableScope.EscapingClosure
      (CallableScope.ScopedSharedLoanCapture captured loan) = false.
Proof.
  intros.
  unfold modeledScopedClosureAccepted.
  now rewrite CallableScope.escaping_scoped_loan_rejects.
Qed.

Theorem contained_source_scoped_capture_passes_scope_gate :
  forall captured loan,
    modeledScopedClosureAccepted
      (CallableScope.ClosureContainedIn loan)
      (CallableScope.ScopedSharedLoanCapture captured loan) = true.
Proof.
  intros.
  unfold modeledScopedClosureAccepted.
  now rewrite CallableScope.exact_scope_scoped_loan_accepts.
Qed.

Print Assumptions exact_native_capture_cut_and_frame.
Print Assumptions native_capture_error_has_no_successor.
Print Assumptions duplicate_linear_source_capture_blocks_move_before_native_use.
Print Assumptions active_scoped_loan_refuses_owner_move_without_successor.
Print Assumptions successful_native_capture_reuse_fails_exactly.
Print Assumptions escaping_source_scoped_capture_has_no_accepted_close.
Print Assumptions contained_source_scoped_capture_passes_scope_gate.
