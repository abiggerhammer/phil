From Stdlib Require Import Strings.String Bool.Bool Lists.List.

From Phil.Core Require Import Syntax Context.
From Phil.Surface Require Import
  SurfaceRepresentedBorrowTrace
  SurfaceBorrowLoanStateCorrespondence
  SurfaceBorrowStepErrorBridge SurfaceObservationProducerFidelity.

Import ListNotations.

(*
  FSEM-01: checker resource-state -> observation refinement, bounded.

  Context.ResourceContext models Haskell finite Map/Set extensionally as
  lookup functions. This module *derives* every observed owner/loan bit
  from Context's actual lookup state and proves correspondence across
  linear loan start, end, and terminal consumption.

  The production Engine observes its Haskell ResourceContext maps via
  BorrowTraceCheckpoint; observeBorrowTraceResource checks the exact
  single-owner Map/Set domain and the source binder identities. CI tests
  that API against real checker snapshots and malformed maps/sets.

  Still open: a language-crossing theorem that Haskell Map.lookup,
  Set.member, and the runtime's ResourceContext transitions refine the
  Rocq Context model for all programs.
*)

Definition observeContext
  (phase : SurfaceRepresentedBorrowTrace.ModeledBorrowPhase)
  (owner : Syntax.Name) (ctx : Context.ResourceContext)
  : SurfaceObservationProducerFidelity.RawCheckpoint :=
  SurfaceObservationProducerFidelity.mkRawCheckpoint phase
    (Context.bindingPresent owner (Context.linearBindings ctx))
    (Context.sharedLoans ctx owner).

Theorem observed_owner_bit_is_actual_linear_lookup :
  forall phase owner ctx,
    SurfaceObservationProducerFidelity.checkpointOwnerPresent
      (observeContext phase owner ctx) =
    Context.bindingPresent owner (Context.linearBindings ctx).
Proof. reflexivity. Qed.

Theorem observed_loan_bit_is_actual_shared_set_membership :
  forall phase owner ctx,
    SurfaceObservationProducerFidelity.checkpointLoanActive
      (observeContext phase owner ctx) =
    Context.sharedLoans ctx owner.
Proof. reflexivity. Qed.

Theorem observed_phase_is_not_inferred_from_resource_bits :
  forall phase owner ctx,
    SurfaceObservationProducerFidelity.checkpointPhase
      (observeContext phase owner ctx) = phase.
Proof. reflexivity. Qed.

Theorem lookup_present_means_observed_present :
  forall phase owner ctx ty,
    Context.linearBindings ctx owner = Some ty ->
    SurfaceObservationProducerFidelity.checkpointOwnerPresent
      (observeContext phase owner ctx) = true.
Proof.
  intros phase owner ctx ty Hty.
  unfold observeContext; simpl.
  unfold Context.bindingPresent.
  now rewrite Hty.
Qed.

Theorem lookup_absent_means_observed_absent :
  forall phase owner ctx,
    Context.linearBindings ctx owner = None ->
    SurfaceObservationProducerFidelity.checkpointOwnerPresent
      (observeContext phase owner ctx) = false.
Proof.
  intros phase owner ctx Hnone.
  unfold observeContext; simpl.
  unfold Context.bindingPresent.
  now rewrite Hnone.
Qed.

Theorem exact_bits_produce_canonical_snapshot :
  forall phase owner ctx,
    Context.bindingPresent owner (Context.linearBindings ctx) =
      fst (SurfaceBorrowStepErrorBridge.expectedOwnerBits phase) ->
    Context.sharedLoans ctx owner =
      snd (SurfaceBorrowStepErrorBridge.expectedOwnerBits phase) ->
    observeContext phase owner ctx =
      SurfaceObservationProducerFidelity.canonicalCheckpoint phase.
Proof.
  intros phase owner ctx Hlinear Hloan.
  unfold observeContext,
    SurfaceObservationProducerFidelity.canonicalCheckpoint.
  now rewrite Hlinear, Hloan.
Qed.

Theorem source_observation_renders_exact_state_bits :
  forall phase owner ctx,
    SurfaceObservationProducerFidelity.renderCheckpoint
      (observeContext phase owner ctx) =
    SurfaceObservationProducerFidelity.checkpointCode phase ++
      (SurfaceObservationProducerFidelity.flagCode
         (Context.bindingPresent owner (Context.linearBindings ctx)) ++
       SurfaceObservationProducerFidelity.flagCode
         (Context.sharedLoans ctx owner)).
Proof. reflexivity. Qed.

Theorem before_loan_observes_real_unloaned_owner :
  forall owner ctx ty,
    Context.linearBindings ctx owner = Some ty ->
    Context.sharedLoans ctx owner = false ->
    observeContext SurfaceRepresentedBorrowTrace.ModelBeforeLoan
      owner ctx =
    SurfaceObservationProducerFidelity.canonicalCheckpoint
      SurfaceRepresentedBorrowTrace.ModelBeforeLoan.
Proof.
  intros owner ctx ty Hty Hfree.
  apply exact_bits_produce_canonical_snapshot.
  - unfold Context.bindingPresent. rewrite Hty. reflexivity.
  - exact Hfree.
Qed.

Theorem after_start_exact_checkpoint :
  forall owner ctx started ty,
    Context.linearBindings ctx owner = Some ty ->
    SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan
      owner ctx = Some started ->
    observeContext SurfaceRepresentedBorrowTrace.ModelLoanStarted
      owner started =
    SurfaceObservationProducerFidelity.canonicalCheckpoint
      SurfaceRepresentedBorrowTrace.ModelLoanStarted.
Proof.
  intros owner ctx started ty Hty Hstart.
  pose proof
    (SurfaceBorrowLoanStateCorrespondence.start_linear_loan_requires_present_unloaned_owner
      owner ctx started Hstart) as [_ [_ [Hloan Hsame]]].
  apply exact_bits_produce_canonical_snapshot.
  - unfold Context.bindingPresent.
    rewrite Hsame, Hty. reflexivity.
  - exact Hloan.
Qed.

Theorem after_end_exact_checkpoint :
  forall owner started closed ty,
    Context.linearBindings started owner = Some ty ->
    SurfaceBorrowLoanStateCorrespondence.endLinearSharedLoan
      owner started = Some closed ->
    observeContext SurfaceRepresentedBorrowTrace.ModelLoanClosed
      owner closed =
    SurfaceObservationProducerFidelity.canonicalCheckpoint
      SurfaceRepresentedBorrowTrace.ModelLoanClosed.
Proof.
  intros owner started closed ty Hty Hend.
  pose proof
    (SurfaceBorrowLoanStateCorrespondence.end_linear_loan_requires_active_owner
      owner started closed Hend) as [_ [Hfree Hsame]].
  apply exact_bits_produce_canonical_snapshot.
  - unfold Context.bindingPresent.
    rewrite Hsame, Hty. reflexivity.
  - exact Hfree.
Qed.

Theorem consumed_owner_exact_terminal_checkpoint :
  forall owner closed returned ty,
    Context.consumeLinear owner closed = Context.Consumed ty returned ->
    Context.sharedLoans closed owner = false ->
    observeContext SurfaceRepresentedBorrowTrace.ModelOwnerReturned
      owner returned =
    SurfaceObservationProducerFidelity.canonicalCheckpoint
      SurfaceRepresentedBorrowTrace.ModelOwnerReturned.
Proof.
  intros owner closed returned ty Hconsume Hfree.
  pose proof
    (Context.consumeLinear_success_exact
      owner closed returned ty Hconsume) as
      [_ [Hnone [_ [_ [_ Hloan]]]]].
  apply exact_bits_produce_canonical_snapshot.
  - unfold Context.bindingPresent.
    rewrite Hnone. reflexivity.
  - rewrite Hloan. exact Hfree.
Qed.

Theorem escape_rejection_cannot_forge_loan_closure :
  forall owner ctx started ty,
    Context.linearBindings ctx owner = Some ty ->
    SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan
      owner ctx = Some started ->
    observeContext SurfaceRepresentedBorrowTrace.ModelEscapeRejected
      owner started =
    SurfaceObservationProducerFidelity.canonicalCheckpoint
      SurfaceRepresentedBorrowTrace.ModelEscapeRejected.
Proof.
  intros owner ctx started ty Hty Hstart.
  pose proof
    (SurfaceBorrowLoanStateCorrespondence.start_linear_loan_requires_present_unloaned_owner
      owner ctx started Hstart) as [_ [_ [Hloan Hsame]]].
  apply exact_bits_produce_canonical_snapshot.
  - unfold Context.bindingPresent.
    rewrite Hsame, Hty. reflexivity.
  - exact Hloan.
Qed.

(* This result is about the precise Rocq Context lookup model, not
   source evaluation, error classification or a global Haskell theorem.
   The Haskell checker-state observer verifies the one-owner Map/Set
   domain separately and must reject unknown keys. *)
