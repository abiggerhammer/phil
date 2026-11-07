From Stdlib Require Import Bool.Bool Lists.List Strings.String.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import
  SurfaceBinderNameEncoding SurfaceDeclarationIdentityBridge
  SurfaceRepresentedBorrowTrace.

Import ListNotations.

(*
  FSEM-01: a bounded and EXPLICIT observational step/error interface.

  We do not assume that Haskell Engine transitions are Rocq transitions.
  Instead, a production checkpoint is *observed* as an owner identity,
  a phase tag, and two resource-membership flags. The Haskell test checks
  this interface against real production checkpoints and exact outcomes.
  This file proves the behavior of the specified small-step checker and
  proves that its error/return states have no successors.

  Catalog identity and Unicode Text-to-String representation are still
  external premises; the source checker is not extracted from this model.
*)

Inductive LoanEvent : Type :=
| EventBegin
| EventBodySafe
| EventBodyEscapes
| EventClose
| EventReturn
| EventRejectBorrowEscape.

Definition nextPhase
  (phase : ModeledBorrowPhase) (event : LoanEvent)
  : option ModeledBorrowPhase :=
  match phase, event with
  | ModelBeforeLoan, EventBegin => Some ModelLoanStarted
  | ModelLoanStarted, EventBodySafe => Some (ModelBodyResult false)
  | ModelLoanStarted, EventBodyEscapes => Some (ModelBodyResult true)
  | ModelBodyResult false, EventClose => Some ModelLoanClosed
  | ModelLoanClosed, EventReturn => Some ModelOwnerReturned
  | ModelBodyResult true, EventRejectBorrowEscape =>
      Some ModelEscapeRejected
  | _, _ => None
  end.

Definition expectedOwnerBits
  (phase : ModeledBorrowPhase) : bool * bool :=
  match phase with
  | ModelBeforeLoan => (true, false)
  | ModelLoanStarted => (true, true)
  | ModelBodyResult _ => (true, true)
  | ModelLoanClosed => (true, false)
  | ModelOwnerReturned => (false, false)
  | ModelEscapeRejected => (true, true)
  end.

Record ObservedLoanCut : Type := mkObservedLoanCut {
  observedOwner : BindingSemantics.BinderKey;
  observedPhase : ModeledBorrowPhase;
  observedLinear : bool;
  observedLoan : bool
}.

Definition modeledCut
  (owner : BindingSemantics.BinderKey)
  (phase : ModeledBorrowPhase) : ObservedLoanCut :=
  mkObservedLoanCut owner phase
    (fst (expectedOwnerBits phase)) (snd (expectedOwnerBits phase)).

Definition wellFormedCut (cut : ObservedLoanCut) : Prop :=
  (observedLinear cut, observedLoan cut) =
    expectedOwnerBits (observedPhase cut).

Definition checkedAdvance
  (cut : ObservedLoanCut) (event : LoanEvent)
  : option ObservedLoanCut :=
  if andb
      (Bool.eqb (observedLinear cut)
        (fst (expectedOwnerBits (observedPhase cut))))
      (Bool.eqb (observedLoan cut)
        (snd (expectedOwnerBits (observedPhase cut))))
  then
    match nextPhase (observedPhase cut) event with
    | Some target => Some (modeledCut (observedOwner cut) target)
    | None => None
    end
  else None.

Definition representedObservation
  (catalog : list string)
  (normalized : BindingSemantics.BinderKey)
  (concrete : SurfaceBinderNameEncoding.TextBinderKey)
  (cut : ObservedLoanCut) : Prop :=
  NoDup catalog /\
  SurfaceDeclarationIdentityBridge.representsBinderKey
    catalog normalized concrete /\
  observedOwner cut = normalized /\
  wellFormedCut cut.

Theorem modeled_cut_well_formed :
  forall owner phase, wellFormedCut (modeledCut owner phase).
Proof.
  intros owner phase.
  destruct phase; reflexivity.
Qed.

Theorem checked_advance_preserves_owner :
  forall cut event next,
    checkedAdvance cut event = Some next ->
    observedOwner next = observedOwner cut.
Proof.
  intros cut event next H.
  unfold checkedAdvance in H.
  destruct (andb
      (Bool.eqb (observedLinear cut)
        (fst (expectedOwnerBits (observedPhase cut))))
      (Bool.eqb (observedLoan cut)
        (snd (expectedOwnerBits (observedPhase cut)))))
    eqn:Hbits; try discriminate.
  destruct (nextPhase (observedPhase cut) event) as [phase |]
    eqn:Hphase; try discriminate.
  inversion H; subst next.
  reflexivity.
Qed.

Theorem checked_advance_is_well_formed :
  forall cut event next,
    checkedAdvance cut event = Some next ->
    wellFormedCut next.
Proof.
  intros cut event next H.
  unfold checkedAdvance in H.
  destruct (andb
      (Bool.eqb (observedLinear cut)
        (fst (expectedOwnerBits (observedPhase cut))))
      (Bool.eqb (observedLoan cut)
        (snd (expectedOwnerBits (observedPhase cut)))))
    eqn:Hbits; try discriminate.
  destruct (nextPhase (observedPhase cut) event) as [phase |]
    eqn:Hphase; try discriminate.
  inversion H; subst next.
  apply modeled_cut_well_formed.
Qed.

Theorem checked_step_preserves_catalog_representation :
  forall catalog normalized concrete cut event next,
    representedObservation catalog normalized concrete cut ->
    checkedAdvance cut event = Some next ->
    representedObservation catalog normalized concrete next.
Proof.
  intros catalog normalized concrete cut event next
    [Hnod [Hrepresented [Howner Hwf]]] Hstep.
  unfold representedObservation.
  split; [exact Hnod |].
  split; [exact Hrepresented |].
  split.
  - rewrite (checked_advance_preserves_owner cut event next Hstep).
    exact Howner.
  - exact (checked_advance_is_well_formed cut event next Hstep).
Qed.

Theorem no_continuation_after_borrow_escape :
  forall cut event,
    observedPhase cut = ModelEscapeRejected ->
    checkedAdvance cut event = None.
Proof.
  intros [owner phase present loan] event Hphase.
  simpl in Hphase.
  subst phase.
  destruct present, loan, event; reflexivity.
Qed.

Theorem no_continuation_after_terminal_return :
  forall cut event,
    observedPhase cut = ModelOwnerReturned ->
    checkedAdvance cut event = None.
Proof.
  intros [owner phase present loan] event Hphase.
  simpl in Hphase.
  subst phase.
  destruct present, loan, event; reflexivity.
Qed.

Fixpoint replay
  (cut : ObservedLoanCut) (events : list LoanEvent)
  : option ObservedLoanCut :=
  match events with
  | [] => Some cut
  | event :: rest =>
      match checkedAdvance cut event with
      | None => None
      | Some next => replay next rest
      end
  end.

Theorem rejection_cannot_replay_nonempty_suffix :
  forall cut event suffix,
    observedPhase cut = ModelEscapeRejected ->
    replay cut (event :: suffix) = None.
Proof.
  intros cut event suffix H.
  simpl.
  rewrite (no_continuation_after_borrow_escape cut event H).
  reflexivity.
Qed.

Theorem terminal_return_cannot_replay_nonempty_suffix :
  forall cut event suffix,
    observedPhase cut = ModelOwnerReturned ->
    replay cut (event :: suffix) = None.
Proof.
  intros cut event suffix H.
  simpl.
  rewrite (no_continuation_after_terminal_return cut event H).
  reflexivity.
Qed.

Theorem accepted_borrow_step_replay :
  forall owner,
    replay (modeledCut owner ModelBeforeLoan)
      [EventBegin; EventBodySafe; EventClose; EventReturn] =
    Some (modeledCut owner ModelOwnerReturned).
Proof. intro owner. reflexivity. Qed.

Theorem rejected_borrow_step_replay :
  forall owner,
    replay (modeledCut owner ModelBeforeLoan)
      [EventBegin; EventBodyEscapes; EventRejectBorrowEscape] =
    Some (modeledCut owner ModelEscapeRejected).
Proof. intro owner. reflexivity. Qed.

Theorem wrong_branch_cannot_close_escaped_body :
  forall owner,
    checkedAdvance (modeledCut owner (ModelBodyResult true))
      EventClose = None.
Proof. intro owner. reflexivity. Qed.

Theorem successful_body_cannot_claim_escape_error :
  forall owner,
    checkedAdvance (modeledCut owner (ModelBodyResult false))
      EventRejectBorrowEscape = None.
Proof. intro owner. reflexivity. Qed.

Inductive ModeledOutcome : Type :=
| ModeledAcceptTerminal
| ModeledRejectBorrowEscape.

Definition classifyTerminal (phase : ModeledBorrowPhase)
  : option ModeledOutcome :=
  match phase with
  | ModelOwnerReturned => Some ModeledAcceptTerminal
  | ModelEscapeRejected => Some ModeledRejectBorrowEscape
  | _ => None
  end.

Theorem rejection_classifies_only_as_borrow_escape :
  forall cut,
    observedPhase cut = ModelEscapeRejected ->
    classifyTerminal (observedPhase cut) =
      Some ModeledRejectBorrowEscape /\
    (forall event, checkedAdvance cut event = None).
Proof.
  intros cut Hphase.
  split.
  - now rewrite Hphase.
  - intro event.
    apply no_continuation_after_borrow_escape.
    exact Hphase.
Qed.

(*
  This models a *checked observation interface*, not source operational
  semantics. In particular, the Haskell observer's actual phase sequence,
  its absence of extra checkpoints after errors, and its BorrowEscape
  classification are independently tested, not assumed/proved here.
*)
