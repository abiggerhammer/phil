From Stdlib Require Import Strings.String.
From Phil.Core Require Import
  Syntax Context SessionStep FSEM02ProtocolHeadProgression
  FSEM02PingSuccessorFreshness.

(* NON-NORMATIVE FSEM-02.  Two admitted local Ping heads, source-derived
   occurrence names and nominal/process authority are externally checked
   premises.  An option-valued pair has no one-sided successful outcome.
   This is not a refinement of native ProcessRendezvous. *)

Definition fsem02PingJointResources
  (senderHead receiverHead : Session)
  (senderOld senderNext receiverOld receiverNext : Name)
  (senderBefore receiverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match fsem02Progression FSEM02Send senderHead
          senderOld senderNext senderBefore,
        fsem02Progression FSEM02Receive receiverHead
          receiverOld receiverNext receiverBefore with
  | StepSucceeded senderAfter, StepSucceeded receiverAfter =>
      Some (senderAfter, receiverAfter)
  | _, _ => None
  end.

Theorem fsem02PingJointRejectsFailedSender :
  forall senderHead receiverHead senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02Progression FSEM02Send senderHead
      senderOld senderNext senderBefore = StepFailed ->
    fsem02PingJointResources senderHead receiverHead
      senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof.
  intros senderHead receiverHead senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore Hfailed.
  unfold fsem02PingJointResources.
  rewrite Hfailed.
  reflexivity.
Qed.

Theorem fsem02PingJointRejectsFailedReceiver :
  forall senderHead receiverHead senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02Progression FSEM02Receive receiverHead
      receiverOld receiverNext receiverBefore = StepFailed ->
    fsem02PingJointResources senderHead receiverHead
      senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof.
  intros senderHead receiverHead senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore Hfailed.
  unfold fsem02PingJointResources.
  rewrite Hfailed.
  destruct (fsem02Progression FSEM02Send senderHead
    senderOld senderNext senderBefore); reflexivity.
Qed.

Theorem fsem02PingJointSuccessProjectsBothSteps :
  forall senderHead receiverHead senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore senderAfter receiverAfter,
    fsem02PingJointResources senderHead receiverHead
      senderOld senderNext receiverOld receiverNext senderBefore receiverBefore
      = Some (senderAfter, receiverAfter) ->
    fsem02Progression FSEM02Send senderHead
      senderOld senderNext senderBefore = StepSucceeded senderAfter /\
    fsem02Progression FSEM02Receive receiverHead
      receiverOld receiverNext receiverBefore = StepSucceeded receiverAfter.
Proof.
  intros senderHead receiverHead senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore senderAfter receiverAfter Hjoint.
  unfold fsem02PingJointResources in Hjoint.
  destruct (fsem02Progression FSEM02Send senderHead
    senderOld senderNext senderBefore) as [| actualSender] eqn:Hsender;
    try discriminate.
  destruct (fsem02Progression FSEM02Receive receiverHead
    receiverOld receiverNext receiverBefore) as [| actualReceiver] eqn:Hreceiver;
    try discriminate.
  inversion Hjoint; subst.
  split; congruence.
Qed.

Theorem fsem02PingJointSuccessConsumesBothAndTypesSuccessors :
  forall senderBinder receiverBinder senderTy receiverTy
         senderCont receiverCont senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore senderAfter receiverAfter,
    fsem02PingJointResources
      (Send senderBinder senderTy senderCont)
      (Receive receiverBinder receiverTy receiverCont)
      senderOld senderNext receiverOld receiverNext senderBefore receiverBefore
      = Some (senderAfter, receiverAfter) ->
    linearBindings senderAfter senderOld = None /\
    linearBindings senderAfter senderNext = Some (endpointType senderCont) /\
    linearBindings receiverAfter receiverOld = None /\
    linearBindings receiverAfter receiverNext = Some (endpointType receiverCont).
Proof.
  intros senderBinder receiverBinder senderTy receiverTy senderCont receiverCont
    senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore senderAfter receiverAfter Hjoint.
  apply fsem02PingJointSuccessProjectsBothSteps in Hjoint.
  destruct Hjoint as [Hsender Hreceiver].
  pose proof (continuing_head_exact_predecessor_and_successor
    FSEM02Send (Send senderBinder senderTy senderCont)
    senderOld senderNext senderBefore senderAfter senderCont
    eq_refl Hsender) as HsenderExact.
  pose proof (continuing_head_exact_predecessor_and_successor
    FSEM02Receive (Receive receiverBinder receiverTy receiverCont)
    receiverOld receiverNext receiverBefore receiverAfter receiverCont
    eq_refl Hreceiver) as HreceiverExact.
  destruct HsenderExact as [_ [_ [HsenderGone [HsenderNext _]]]].
  destruct HreceiverExact as [_ [_ [HreceiverGone [HreceiverNext _]]]].
  repeat split; assumption.
Qed.

Theorem fsem02PingJointSuccessFramesBothAffineAndLoans :
  forall senderBinder receiverBinder senderTy receiverTy
         senderCont receiverCont senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore senderAfter receiverAfter,
    fsem02PingJointResources
      (Send senderBinder senderTy senderCont)
      (Receive receiverBinder receiverTy receiverCont)
      senderOld senderNext receiverOld receiverNext senderBefore receiverBefore
      = Some (senderAfter, receiverAfter) ->
    affineBindings senderAfter = affineBindings senderBefore /\
    sharedLoans senderAfter = sharedLoans senderBefore /\
    affineBindings receiverAfter = affineBindings receiverBefore /\
    sharedLoans receiverAfter = sharedLoans receiverBefore.
Proof.
  intros senderBinder receiverBinder senderTy receiverTy senderCont receiverCont
    senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore senderAfter receiverAfter Hjoint.
  apply fsem02PingJointSuccessProjectsBothSteps in Hjoint.
  destruct Hjoint as [Hsender Hreceiver].
  pose proof (fsem02PingContinuationPreservesAffineAndLoans
    FSEM02Send (Send senderBinder senderTy senderCont)
    senderOld senderNext senderBefore senderAfter senderCont
    eq_refl Hsender) as [HsenderAffine HsenderLoans].
  pose proof (fsem02PingContinuationPreservesAffineAndLoans
    FSEM02Receive (Receive receiverBinder receiverTy receiverCont)
    receiverOld receiverNext receiverBefore receiverAfter receiverCont
    eq_refl Hreceiver) as [HreceiverAffine HreceiverLoans].
  repeat split; assumption.
Qed.


(* FSEM-02: nonterminal Send/Receive resource agreement is a separate,
   externally checked native premise. The finite Rocq ResourceContext has
   an abstract endpointType token, not the actual Haskell TyEndpoint session
   constructor. These boolean gates therefore do NOT prove resource-map
   correspondence or turn forged metadata into protocol authority. *)
Definition fsem02PingJointResourceAdmission
  (senderAgrees receiverAgrees : bool)
  (senderHead receiverHead : Session)
  (senderOld senderNext receiverOld receiverNext : Name)
  (senderBefore receiverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  if senderAgrees then
    if receiverAgrees then
      fsem02PingJointResources senderHead receiverHead
        senderOld senderNext receiverOld receiverNext
        senderBefore receiverBefore
    else None
  else None.

Theorem fsem02PingJointRejectsDisagreedSender :
  forall receiverAgrees senderHead receiverHead
         senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02PingJointResourceAdmission false receiverAgrees
      senderHead receiverHead senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof. reflexivity. Qed.

Theorem fsem02PingJointRejectsDisagreedReceiver :
  forall senderAgrees senderHead receiverHead
         senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02PingJointResourceAdmission senderAgrees false
      senderHead receiverHead senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof. intros. destruct senderAgrees; reflexivity. Qed.

Theorem fsem02PingJointRejectsMissingSenderPredecessor :
  forall senderAgrees receiverAgrees senderHead receiverHead
         senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    linearBindings senderBefore senderOld = None ->
    fsem02PingJointResourceAdmission senderAgrees receiverAgrees
      senderHead receiverHead senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof.
  intros senderAgrees receiverAgrees senderHead receiverHead
    senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore Hmissing.
  unfold fsem02PingJointResourceAdmission.
  destruct senderAgrees; [|reflexivity].
  destruct receiverAgrees; [|reflexivity].
  apply fsem02PingJointRejectsFailedSender.
  destruct (fsem02Progression FSEM02Send senderHead
    senderOld senderNext senderBefore) as [| actualAfter] eqn:Hstep.
  - reflexivity.
  - exfalso.
    eapply (stale_linear_predecessor_cannot_succeed
      FSEM02Send senderHead senderOld senderNext
      senderBefore actualAfter Hmissing).
    exact Hstep.
Qed.

Theorem fsem02PingJointRejectsMissingReceiverPredecessor :
  forall senderAgrees receiverAgrees senderHead receiverHead
         senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    linearBindings receiverBefore receiverOld = None ->
    fsem02PingJointResourceAdmission senderAgrees receiverAgrees
      senderHead receiverHead senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof.
  intros senderAgrees receiverAgrees senderHead receiverHead
    senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore Hmissing.
  unfold fsem02PingJointResourceAdmission.
  destruct senderAgrees; [|reflexivity].
  destruct receiverAgrees; [|reflexivity].
  apply fsem02PingJointRejectsFailedReceiver.
  destruct (fsem02Progression FSEM02Receive receiverHead
    receiverOld receiverNext receiverBefore) as [| actualAfter] eqn:Hstep.
  - reflexivity.
  - exfalso.
    eapply (stale_linear_predecessor_cannot_succeed
      FSEM02Receive receiverHead receiverOld receiverNext
      receiverBefore actualAfter Hmissing).
    exact Hstep.
Qed.

Theorem fsem02PingJointAdmittedSuccessExactAndFrame :
  forall senderAgrees receiverAgrees
         senderBinder receiverBinder senderTy receiverTy
         senderCont receiverCont senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore senderAfter receiverAfter,
    fsem02PingJointResourceAdmission senderAgrees receiverAgrees
      (Send senderBinder senderTy senderCont)
      (Receive receiverBinder receiverTy receiverCont)
      senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = Some (senderAfter, receiverAfter) ->
    senderAgrees = true /\\
    receiverAgrees = true /\\
    linearBindings senderAfter senderOld = None /\\
    linearBindings senderAfter senderNext = Some (endpointType senderCont) /\\
    linearBindings receiverAfter receiverOld = None /\\
    linearBindings receiverAfter receiverNext = Some (endpointType receiverCont) /\\
    affineBindings senderAfter = affineBindings senderBefore /\\
    sharedLoans senderAfter = sharedLoans senderBefore /\\
    affineBindings receiverAfter = affineBindings receiverBefore /\\
    sharedLoans receiverAfter = sharedLoans receiverBefore.
Proof.
  intros senderAgrees receiverAgrees
    senderBinder receiverBinder senderTy receiverTy senderCont receiverCont
    senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore senderAfter receiverAfter Hstep.
  unfold fsem02PingJointResourceAdmission in Hstep.
  destruct senderAgrees; try discriminate.
  destruct receiverAgrees; try discriminate.
  pose proof (fsem02PingJointSuccessConsumesBothAndTypesSuccessors
    senderBinder receiverBinder senderTy receiverTy
    senderCont receiverCont senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore senderAfter receiverAfter Hstep)
    as [HsenderOld [HsenderNext [HreceiverOld HreceiverNext]]].
  pose proof (fsem02PingJointSuccessFramesBothAffineAndLoans
    senderBinder receiverBinder senderTy receiverTy
    senderCont receiverCont senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore senderAfter receiverAfter Hstep)
    as [HsenderAffine [HsenderLoans [HreceiverAffine HreceiverLoans]]].
  repeat split; try reflexivity; assumption.
Qed.
