From Stdlib Require Import Bool.Bool Lists.List Strings.String.
Import ListNotations.
From Phil.Core Require Import GenericStructural CallableMode CallableScope Context Syntax.

(* Bounded conditional source capture model. Concrete Haskell parser and
   Map/Set fidelity are separately tested, not proved universally. *)
Theorem source_linear_capture_must_move :
  forall occurrence transfer,
    CallableMode.captureTransferAllowed
      (CallableMode.mkClosureCapture occurrence transfer GenericStructural.Linear) = true ->
    transfer = CallableMode.MoveCapture.
Proof. exact CallableMode.accepted_linear_capture_must_move. Qed.

Theorem source_unrestricted_capture_can_copy :
  forall occurrence,
    CallableMode.captureTransferAllowed
      (CallableMode.mkClosureCapture occurrence CallableMode.CopyCapture
        GenericStructural.Unrestricted) = true.
Proof. exact CallableMode.unrestricted_capture_may_copy. Qed.

Theorem source_duplicate_linear_capture_rejects :
  forall occurrence first second,
    CallableMode.duplicateCaptureAllowed
      (CallableMode.mkClosureCapture occurrence first GenericStructural.Linear)
      (CallableMode.mkClosureCapture occurrence second GenericStructural.Linear) = false.
Proof. exact CallableMode.duplicate_linear_occurrence_is_rejected. Qed.

Theorem source_capture_consumes_exact_linear_owner :
  forall (old : Syntax.Name) (before after : Context.ResourceContext)
         (ty : Syntax.Ty),
    Context.consumeLinear old before = Context.Consumed ty after ->
    Context.linearBindings before old = Some ty /\
    Context.linearBindings after old = None.
Proof.
  intros old before after ty Hmove.
  pose proof (Context.consumeLinear_success_exact old before after ty Hmove)
    as [Hbefore [Hafter _]].
  now split.
Qed.

Theorem source_capture_preserves_other_linear :
  forall (old other : Syntax.Name)
         (before after : Context.ResourceContext) (ty : Syntax.Ty),
    String.eqb other old = false ->
    Context.consumeLinear old before = Context.Consumed ty after ->
    Context.linearBindings after other =
      Context.linearBindings before other.
Proof.
  intros old other before after ty Hneq Hmove.
  eapply Context.consumeLinear_success_preserves_other_linear; eauto.
Qed.

Theorem source_borrowed_owner_cannot_move :
  forall (owner : Syntax.Name) (before : Context.ResourceContext),
    Context.sharedLoans before owner = true ->
    Context.consumeLinear owner before =
      Context.ConsumeError (Context.OwnerBorrowed owner).
Proof.
  intros owner before Hloan. unfold Context.consumeLinear.
  now rewrite Hloan.
Qed.

Theorem source_local_scoped_capture_allowed :
  forall view loan,
    CallableScope.decideClosureScopeCapture
      (CallableScope.ClosureContainedIn loan)
      (CallableScope.ScopedSharedLoanCapture view loan) =
        CallableScope.ScopeCaptureAccepted.
Proof. exact CallableScope.exact_scope_scoped_loan_accepts. Qed.

Theorem source_escaping_scoped_capture_rejected :
  forall view loan,
    CallableScope.decideClosureScopeCapture
      CallableScope.EscapingClosure
      (CallableScope.ScopedSharedLoanCapture view loan) =
        CallableScope.ScopeCaptureEscapingLoan.
Proof. exact CallableScope.escaping_scoped_loan_rejects. Qed.

Theorem conditional_hidden_restricted_cycle_rejected :
  forall nodes,
    ~ CallableScope.noRestrictedClosureCycles nodes ->
    ~ CallableScope.recursiveClosureGraphValid nodes.
Proof.
  intros nodes Hnot Hvalid.
  apply Hnot.
  exact (proj2 (proj2 Hvalid)).
Qed.

Print Assumptions source_linear_capture_must_move.
Print Assumptions source_unrestricted_capture_can_copy.
Print Assumptions source_duplicate_linear_capture_rejects.
Print Assumptions source_capture_consumes_exact_linear_owner.
Print Assumptions source_capture_preserves_other_linear.
Print Assumptions source_borrowed_owner_cannot_move.
Print Assumptions source_local_scoped_capture_allowed.
Print Assumptions source_escaping_scoped_capture_rejected.
Print Assumptions conditional_hidden_restricted_cycle_rejected.
