From Stdlib Require Import Strings.String Bool.Bool.

From Phil.Core Require Import Syntax Context.
From Phil.Surface Require Import SurfaceFiniteContextFrame
  SurfaceSourceAffineBridge.

(*
  FSEM-01 mixed affine/linear: model consequences for two distinct source
  identities after admitted affine nominal mode checking. The Haskell test
  executes one real two-parameter Grammar-v1 function, not these definitions.
  No universal Text/Map/Set implementation refinement, independent
  attestation proof, full satisfies C, or native CheckError simulation follows.
*)

Theorem mixed_affine_mode_needs_external_admission :
  forall sourceMode admitted,
    SurfaceSourceAffineBridge.checkedSourceAffineMode
      sourceMode admitted = Some Syntax.Affine ->
    sourceMode = Syntax.Affine /\ admitted = true.
Proof.
  intros mode admitted Hchecked.
  now apply SurfaceSourceAffineBridge.source_affine_requires_admitted_evidence.
Qed.

(* The shared loan of an affine owner cannot alter the linear spectator,
   nor the spectator's independent loan bit. *)
Theorem mixed_affine_loan_frames_linear_spectator :
  forall permit payload payloadTy before borrowed,
    String.eqb payload permit = false ->
    Context.linearBindings before payload = Some payloadTy ->
    SurfaceFiniteContextFrame.startOwnedLoanModel permit before =
      Some borrowed ->
    Context.linearBindings borrowed payload = Some payloadTy /\
    Context.sharedLoans borrowed payload =
      Context.sharedLoans before payload /\
    Context.sharedLoans borrowed permit = true.
Proof.
  intros permit payload payloadTy before borrowed Hdistinct Hlinear Hstart.
  pose proof
    (SurfaceFiniteContextFrame.successful_loan_start_frames_any_finite_context
      permit before borrowed Hstart) as Hframe.
  specialize (Hframe payload Hdistinct).
  destruct Hframe as [_ [_ [HlinearFrame HloanFrame]]].
  pose proof
    (SurfaceFiniteContextFrame.successful_loan_start_activates_exact_owner
      permit before borrowed Hstart) as Hactive.
  split.
  - now rewrite HlinearFrame.
  - split; assumption.
Qed.

(* Borrowing affine Permit blocks its consumption, but cannot consume or
   accidentally satisfy a separate Bytes[N] linear obligation. *)
Theorem mixed_borrowed_affine_still_owes_linear_spectator :
  forall permit payload payloadTy before borrowed,
    String.eqb payload permit = false ->
    Context.linearBindings before payload = Some payloadTy ->
    SurfaceFiniteContextFrame.startOwnedLoanModel permit before =
      Some borrowed ->
    SurfaceFiniteContextFrame.consumeAffineModel permit borrowed = None /\
    Context.linearBindings borrowed payload = Some payloadTy.
Proof.
  intros permit payload payloadTy before borrowed Hneq Hlinear Hstart.
  pose proof
    (SurfaceSourceAffineBridge.source_affine_borrow_blocks_consumption
      permit before borrowed Hstart) as [_ [Hblocked Hframe]].
  specialize (Hframe payload Hneq).
  destruct Hframe as [_ [_ [HlinearFrame _]]].
  split.
  - exact Hblocked.
  - now rewrite HlinearFrame.
Qed.

(* An independent linear move leaves the borrowed affine owner present,
   including its active shared loan, in every other owner zone. *)
Theorem mixed_linear_move_preserves_affine_owner_and_loan :
  forall permit payload permitTy payloadTy before after,
    String.eqb permit payload = false ->
    Context.affineBindings before permit = Some permitTy ->
    Context.sharedLoans before permit = true ->
    Context.consumeLinear payload before = Context.Consumed payloadTy after ->
    Context.affineBindings after permit = Some permitTy /\
    Context.sharedLoans after permit = true.
Proof.
  intros permit payload permitTy payloadTy before after
    Hdistinct Haffine Hloan Hconsume.
  pose proof
    (SurfaceFiniteContextFrame.successful_linear_consume_frames_any_finite_context
      payload payloadTy before after Hconsume) as Hframe.
  specialize (Hframe permit Hdistinct).
  destruct Hframe as [_ [HaffineFrame [_ HloanFrame]]].
  split.
  - now rewrite HaffineFrame.
  - now rewrite HloanFrame.
Qed.

(* Closing a loan to Permit does not silently consume a linear payload. *)
Theorem mixed_affine_loan_close_keeps_linear_debt :
  forall permit payload payloadTy before closed,
    String.eqb payload permit = false ->
    Context.linearBindings before payload = Some payloadTy ->
    SurfaceFiniteContextFrame.endOwnedLoanModel permit before =
      Some closed ->
    Context.linearBindings closed payload = Some payloadTy.
Proof.
  intros permit payload payloadTy before closed Hdistinct Hlinear Hend.
  pose proof
    (SurfaceFiniteContextFrame.successful_loan_end_frames_any_finite_context
      permit before closed Hend) as Hframe.
  specialize (Hframe payload Hdistinct).
  destruct Hframe as [_ [_ [HlinearFrame _]]].
  now rewrite HlinearFrame.
Qed.

(* Dropping an unloaned affine owner is allowed in this model; it does NOT
   discharge a still-live independent linear binding. A native program whose
   linear owner remains at exit fails Core.ensureComplete, tested in Haskell. *)
Theorem mixed_affine_discard_preserves_linear_debt :
  forall permit payload payloadTy before after,
    Context.linearBindings before payload = Some payloadTy ->
    SurfaceSourceAffineBridge.discardUnloanedAffineModel permit before =
      Some after ->
    Context.affineBindings after permit = None /\
    Context.linearBindings after payload = Some payloadTy.
Proof.
  intros permit payload payloadTy before after Hlinear Hdrop.
  pose proof
    (SurfaceSourceAffineBridge.successful_affine_discard_is_exact_and_frames
      permit before after Hdrop) as [Haffine [HlinearFrame _]].
  split.
  - exact Haffine.
  - now rewrite HlinearFrame.
Qed.

Print Assumptions mixed_affine_mode_needs_external_admission.
Print Assumptions mixed_affine_loan_frames_linear_spectator.
Print Assumptions mixed_borrowed_affine_still_owes_linear_spectator.
Print Assumptions mixed_linear_move_preserves_affine_owner_and_loan.
Print Assumptions mixed_affine_loan_close_keeps_linear_debt.
Print Assumptions mixed_affine_discard_preserves_linear_debt.
