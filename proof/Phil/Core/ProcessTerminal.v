From Stdlib Require Import Strings.String.

From Phil.Core Require Import Syntax Context.

(*
  Proof-oriented model of Phil.Core.Process.terminalFlow / ensureComplete.

  The implementation decides emptiness using Data.Set.null and Data.Map.null.
  The existing proof-side ResourceContext represents sets and maps extensionally,
  so this slice states the successful semantic boundary observationally: a
  complete resource context has no name with a live loan and no name with a
  linear binding. This is exactly the condition required before Closed or Failed
  may be constructed by terminalFlow.

  Return is intentionally outside this model. Phil.Core.Process.returnFlow uses
  ensureReturnable, whose current criterion is only that no shared loan escapes;
  it does not require all linear resources to have been consumed.
*)

Definition NoActiveLoans (context : ResourceContext) : Prop :=
  forall name : Name, sharedLoans context name = false.

Definition NoLinearResources (context : ResourceContext) : Prop :=
  forall name : Name, linearBindings context name = None.

Definition ResourceComplete (context : ResourceContext) : Prop :=
  NoActiveLoans context /\ NoLinearResources context.

(* Successful semantic result of Context.ensureComplete. *)
Inductive EnsureCompleteSuccess : ResourceContext -> Prop :=
| EnsureComplete_ok :
    forall context,
      NoActiveLoans context ->
      NoLinearResources context ->
      EnsureCompleteSuccess context.

Inductive TerminalFlowSuccess : Control -> ResourceContext -> Prop :=
| TerminalFlow_closed :
    forall outcome context,
      EnsureCompleteSuccess context ->
      TerminalFlowSuccess (Closed outcome) context
| TerminalFlow_failed :
    forall failureClass detail context,
      EnsureCompleteSuccess context ->
      TerminalFlowSuccess (Failed failureClass detail) context.

Lemma ensure_complete_success_exact :
  forall context,
    EnsureCompleteSuccess context <-> ResourceComplete context.
Proof.
  intros context.
  split.
  - intro Hcomplete.
    inversion Hcomplete; subst.
    split; assumption.
  - intros [Hloans Hlinear].
    constructor; assumption.
Qed.

(*
  PHIL-PROC-TERM-001.

  Closed and Failed paths can be constructed successfully only from a resource
  context with no live shared loans and no remaining linear owners.
*)
Theorem terminal_flow_success_requires_resource_complete :
  forall control context,
    TerminalFlowSuccess control context ->
    ResourceComplete context.
Proof.
  intros control context Hterminal.
  inversion Hterminal; subst;
    apply ensure_complete_success_exact;
    assumption.
Qed.

Corollary terminal_flow_success_has_no_loans :
  forall control context,
    TerminalFlowSuccess control context ->
    NoActiveLoans context.
Proof.
  intros control context Hterminal.
  pose proof
    (terminal_flow_success_requires_resource_complete control context Hterminal)
    as [Hloans _].
  exact Hloans.
Qed.

Corollary terminal_flow_success_has_no_linear_resources :
  forall control context,
    TerminalFlowSuccess control context ->
    NoLinearResources context.
Proof.
  intros control context Hterminal.
  pose proof
    (terminal_flow_success_requires_resource_complete control context Hterminal)
    as [_ Hlinear].
  exact Hlinear.
Qed.

(* PHIL-PROC-TERM-001: successful terminalFlow cannot construct Return. *)
Theorem terminal_flow_never_returns :
  forall returnTy context,
    ~ TerminalFlowSuccess (Return returnTy) context.
Proof.
  intros returnTy context Hterminal.
  inversion Hterminal.
Qed.

(* PHIL-PROC-TERM-001: successful terminalFlow cannot construct Continue. *)
Theorem terminal_flow_never_continues :
  forall context,
    ~ TerminalFlowSuccess Continue context.
Proof.
  intros context Hterminal.
  inversion Hterminal.
Qed.

(* Completeness is sufficient for either terminal constructor. *)
Theorem resource_complete_allows_closed :
  forall outcome context,
    ResourceComplete context ->
    TerminalFlowSuccess (Closed outcome) context.
Proof.
  intros outcome context Hcomplete.
  constructor.
  apply ensure_complete_success_exact.
  exact Hcomplete.
Qed.

Theorem resource_complete_allows_failed :
  forall failureClass detail context,
    ResourceComplete context ->
    TerminalFlowSuccess (Failed failureClass detail) context.
Proof.
  intros failureClass detail context Hcomplete.
  constructor.
  apply ensure_complete_success_exact.
  exact Hcomplete.
Qed.
