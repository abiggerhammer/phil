From Phil.Core Require Import Syntax Context SessionStep ConcurrencySemantics
  FSEM02PingJointAtomicity.

(* Non-normative finite admission model: source-checked Ping endpoint
   predecessor/successor identity, external process instance, role/projection
   and native resource agreement remain independently supplied premises.
   In particular, the Haskell diagnostic constructors are NOT extracted from
   this model. Only the order of these explicitly named gates is modeled. *)
Inductive FSEM02PingJointGateClass : Type :=
| FSEM02SenderNominalRefused
| FSEM02SenderProjectionRefused
| FSEM02ReceiverNominalRefused
| FSEM02ReceiverProjectionRefused
| FSEM02SenderResourceRefused
| FSEM02ReceiverResourceRefused
| FSEM02JointGatesAdmitted.

Definition fsem02PingJointClassify
  (senderNominal senderProjection receiverNominal receiverProjection
   senderResource receiverResource : bool) : FSEM02PingJointGateClass :=
  if senderNominal then
    if senderProjection then
      if receiverNominal then
        if receiverProjection then
          if senderResource then
            if receiverResource then FSEM02JointGatesAdmitted
            else FSEM02ReceiverResourceRefused
          else FSEM02SenderResourceRefused
        else FSEM02ReceiverProjectionRefused
      else FSEM02ReceiverNominalRefused
    else FSEM02SenderProjectionRefused
  else FSEM02SenderNominalRefused.

Theorem fsem02PingJointSenderNominalFirst :
  forall sh rn rh sr rr,
    fsem02PingJointClassify false sh rn rh sr rr =
      FSEM02SenderNominalRefused.
Proof. reflexivity. Qed.

Theorem fsem02PingJointSenderProjectionBeforeReceiverNominal :
  forall rn rh sr rr,
    fsem02PingJointClassify true false rn rh sr rr =
      FSEM02SenderProjectionRefused.
Proof. reflexivity. Qed.

Theorem fsem02PingJointReceiverNominalBeforeSenderResources :
  forall rh sr rr,
    fsem02PingJointClassify true true false rh sr rr =
      FSEM02ReceiverNominalRefused.
Proof. reflexivity. Qed.

Theorem fsem02PingJointReceiverProjectionBeforeSenderResources :
  forall sr rr,
    fsem02PingJointClassify true true true false sr rr =
      FSEM02ReceiverProjectionRefused.
Proof. reflexivity. Qed.

Theorem fsem02PingJointSenderResourceBeforeReceiverResource :
  forall rr,
    fsem02PingJointClassify true true true true false rr =
      FSEM02SenderResourceRefused.
Proof. reflexivity. Qed.

Theorem fsem02PingJointRestoredSenderExposesReceiverResource :
  fsem02PingJointClassify true true true true true false =
    FSEM02ReceiverResourceRefused.
Proof. reflexivity. Qed.

Theorem fsem02PingJointAllGatesReady :
  fsem02PingJointClassify true true true true true true =
    FSEM02JointGatesAdmitted.
Proof. reflexivity. Qed.

Theorem fsem02PingJointReadyRequiresEveryPremise :
  forall sn sh rn rh sr rr,
    fsem02PingJointClassify sn sh rn rh sr rr =
      FSEM02JointGatesAdmitted ->
    sn = true /\ sh = true /\ rn = true /\ rh = true /\
    sr = true /\ rr = true.
Proof.
  intros sn sh rn rh sr rr Hready.
  destruct sn, sh, rn, rh, sr, rr; simpl in Hready;
    try discriminate; repeat split; reflexivity.
Qed.

(* The classifier is purely diagnostic. The separate conditional transition
   is exactly the previously checked resource model after all nominal and
   projection premises are supplied; no Haskell map simulation is inferred. *)
Definition fsem02PingJointGatedStep
  (sn sh rn rh sr rr : bool)
  (senderHead receiverHead : Session)
  (senderOld senderNext receiverOld receiverNext : Name)
  (senderBefore receiverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  if sn then
    if sh then
      if rn then
        if rh then
          fsem02PingJointResourceAdmission sr rr
            senderHead receiverHead senderOld senderNext
            receiverOld receiverNext senderBefore receiverBefore
        else None
      else None
    else None
  else None.

Theorem fsem02PingJointGatedStepReducesToResourceAdmission :
  forall sr rr senderHead receiverHead senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore,
    fsem02PingJointGatedStep true true true true sr rr
      senderHead receiverHead senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore =
    fsem02PingJointResourceAdmission sr rr
      senderHead receiverHead senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore.
Proof. reflexivity. Qed.

Theorem fsem02PingJointGatedStepRejectsForeignReceiver :
  forall sh rh sr rr senderHead receiverHead
         senderOld senderNext receiverOld receiverNext senderBefore receiverBefore,
    fsem02PingJointGatedStep true sh false rh sr rr
      senderHead receiverHead senderOld senderNext receiverOld receiverNext
      senderBefore receiverBefore = None.
Proof. intros. destruct sh; reflexivity. Qed.
