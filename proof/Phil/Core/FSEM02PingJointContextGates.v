From Phil.Core Require Import Syntax Context SessionStep FSEM02PingJointAtomicity.

(* FSEM-02: conditional process-context admission ahead of resource agreement.
   Both presence booleans are external observations of the native process map,
   not source-derived authority or a Haskell Map-to-Rocq refinement theorem. *)
Definition fsem02PingJointContextAdmission
  (senderPresent receiverPresent senderAgrees receiverAgrees : bool)
  (senderHead receiverHead : Session)
  (senderOld senderNext receiverOld receiverNext : Name)
  (senderBefore receiverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  if senderPresent then
    if receiverPresent then
      fsem02PingJointResourceAdmission senderAgrees receiverAgrees
        senderHead receiverHead senderOld senderNext receiverOld receiverNext
        senderBefore receiverBefore
    else None
  else None.

Theorem fsem02PingJointMissingSenderContextRefuses :
  forall receiverPresent senderAgrees receiverAgrees
         senderHead receiverHead senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02PingJointContextAdmission false receiverPresent
      senderAgrees receiverAgrees senderHead receiverHead
      senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof. reflexivity. Qed.

Theorem fsem02PingJointMissingReceiverContextRefuses :
  forall senderPresent senderAgrees receiverAgrees
         senderHead receiverHead senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02PingJointContextAdmission senderPresent false
      senderAgrees receiverAgrees senderHead receiverHead
      senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof. intros. destruct senderPresent; reflexivity. Qed.

Theorem fsem02PingJointRestoredContextExposesResourceGate :
  forall senderAgrees receiverAgrees senderHead receiverHead
         senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02PingJointContextAdmission true true
      senderAgrees receiverAgrees senderHead receiverHead
      senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore =
    fsem02PingJointResourceAdmission senderAgrees receiverAgrees
      senderHead receiverHead senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore.
Proof. reflexivity. Qed.

Theorem fsem02PingJointRestoredContextStillRejectsSenderResource :
  forall receiverAgrees senderHead receiverHead
         senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02PingJointContextAdmission true true
      false receiverAgrees senderHead receiverHead
      senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof. reflexivity. Qed.

Theorem fsem02PingJointRestoredContextStillRejectsReceiverResource :
  forall senderAgrees senderHead receiverHead
         senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02PingJointContextAdmission true true
      senderAgrees false senderHead receiverHead
      senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof. intros. destruct senderAgrees; reflexivity. Qed.

Theorem fsem02PingJointContextSuccessRequiresBothContexts :
  forall senderPresent receiverPresent senderAgrees receiverAgrees
         senderHead receiverHead senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore senderAfter receiverAfter,
    fsem02PingJointContextAdmission senderPresent receiverPresent
      senderAgrees receiverAgrees senderHead receiverHead
      senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = Some (senderAfter, receiverAfter) ->
    senderPresent = true /\
    receiverPresent = true /\
    fsem02PingJointResourceAdmission senderAgrees receiverAgrees
      senderHead receiverHead senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = Some (senderAfter, receiverAfter).
Proof.
  intros senderPresent receiverPresent senderAgrees receiverAgrees
    senderHead receiverHead senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore senderAfter receiverAfter Hstep.
  unfold fsem02PingJointContextAdmission in Hstep.
  destruct senderPresent; try discriminate.
  destruct receiverPresent; try discriminate.
  repeat split; try reflexivity; exact Hstep.
Qed.

(* The exact two-owner resource properties follow only after the external
   context-presence premises have been discharged. *)
Theorem fsem02PingJointContextSuccessExactAndFrame :
  forall senderPresent receiverPresent senderAgrees receiverAgrees
         senderBinder receiverBinder senderTy receiverTy
         senderCont receiverCont senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore senderAfter receiverAfter,
    fsem02PingJointContextAdmission senderPresent receiverPresent
      senderAgrees receiverAgrees
      (Send senderBinder senderTy senderCont)
      (Receive receiverBinder receiverTy receiverCont)
      senderOld senderNext receiverOld receiverNext senderBefore receiverBefore
      = Some (senderAfter, receiverAfter) ->
    senderPresent = true /\
    receiverPresent = true /\
    senderAgrees = true /\
    receiverAgrees = true /\
    linearBindings senderAfter senderOld = None /\
    linearBindings senderAfter senderNext = Some (endpointType senderCont) /\
    linearBindings receiverAfter receiverOld = None /\
    linearBindings receiverAfter receiverNext = Some (endpointType receiverCont) /\
    affineBindings senderAfter = affineBindings senderBefore /\
    sharedLoans senderAfter = sharedLoans senderBefore /\
    affineBindings receiverAfter = affineBindings receiverBefore /\
    sharedLoans receiverAfter = sharedLoans receiverBefore.
Proof.
  intros senderPresent receiverPresent senderAgrees receiverAgrees
    senderBinder receiverBinder senderTy receiverTy
    senderCont receiverCont senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore senderAfter receiverAfter Hstep.
  pose proof (fsem02PingJointContextSuccessRequiresBothContexts
    senderPresent receiverPresent senderAgrees receiverAgrees
    (Send senderBinder senderTy senderCont)
    (Receive receiverBinder receiverTy receiverCont)
    senderOld senderNext receiverOld receiverNext senderBefore receiverBefore
    senderAfter receiverAfter Hstep) as [Hsender [Hreceiver Hadmission]].
  pose proof (fsem02PingJointAdmittedSuccessExactAndFrame
    senderAgrees receiverAgrees
    senderBinder receiverBinder senderTy receiverTy senderCont receiverCont
    senderOld senderNext receiverOld receiverNext
    senderBefore receiverBefore senderAfter receiverAfter Hadmission)
    as [HsenderGate [HreceiverGate
      [HsenderOld [HsenderNext [HreceiverOld [HreceiverNext
        [HsenderAffine [HsenderLoans [HreceiverAffine HreceiverLoans]]]]]]]]].
  repeat split; assumption.
Qed.
