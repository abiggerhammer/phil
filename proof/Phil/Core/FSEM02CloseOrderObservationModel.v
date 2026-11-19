From Stdlib Require Import Lists.List Bool.Bool.
(* NON-NORMATIVE FSEM-02 finite Close-order model. These booleans model only
   two explicitly distinct endpoint occurrences and framed payload/spectator.
   They do NOT establish fidelity of Haskell Maps or external Close authority. *)
Inductive FSEM02CloseOrderTag :=
| FSEM02SenderFirstConverged
| FSEM02ReceiverFirstConverged
| FSEM02StaleEndpointRefused.

Definition fsem02CloseOrderConverged (tag : FSEM02CloseOrderTag) : bool :=
  match tag with
  | FSEM02SenderFirstConverged | FSEM02ReceiverFirstConverged => true
  | FSEM02StaleEndpointRefused => false
  end.

Record FSEM02CloseOwnerState := {
  fsem02SenderLive : bool;
  fsem02ReceiverLive : bool;
  fsem02PayloadPresent : bool;
  fsem02SpectatorPresent : bool
}.

Definition fsem02CloseSender (s : FSEM02CloseOwnerState)
  : option FSEM02CloseOwnerState :=
  if fsem02SenderLive s then
    Some {| fsem02SenderLive := false;
            fsem02ReceiverLive := fsem02ReceiverLive s;
            fsem02PayloadPresent := fsem02PayloadPresent s;
            fsem02SpectatorPresent := fsem02SpectatorPresent s |}
  else None.

Definition fsem02CloseReceiver (s : FSEM02CloseOwnerState)
  : option FSEM02CloseOwnerState :=
  if fsem02ReceiverLive s then
    Some {| fsem02SenderLive := fsem02SenderLive s;
            fsem02ReceiverLive := false;
            fsem02PayloadPresent := fsem02PayloadPresent s;
            fsem02SpectatorPresent := fsem02SpectatorPresent s |}
  else None.

Theorem fsem02CloseOwnerOrderCommutes :
  forall s senderHalf senderFinal,
    fsem02CloseSender s = Some senderHalf ->
    fsem02CloseReceiver senderHalf = Some senderFinal ->
    exists receiverHalf,
      fsem02CloseReceiver s = Some receiverHalf /\
      fsem02CloseSender receiverHalf = Some senderFinal.
Proof.
  intros [sender receiver payload spectator] senderHalf senderFinal Hsender Hreceiver.
  simpl in Hsender.
  destruct sender; try discriminate.
  inversion Hsender; subst senderHalf; clear Hsender.
  simpl in Hreceiver.
  destruct receiver; try discriminate.
  inversion Hreceiver; subst senderFinal; clear Hreceiver.
  exists {| fsem02SenderLive := true; fsem02ReceiverLive := false;
            fsem02PayloadPresent := payload;
            fsem02SpectatorPresent := spectator |}.
  split; reflexivity.
Qed.

Theorem fsem02CloseOwnerFrame :
  forall s s',
    fsem02CloseSender s = Some s' ->
    fsem02PayloadPresent s' = fsem02PayloadPresent s /\
    fsem02SpectatorPresent s' = fsem02SpectatorPresent s.
Proof.
  intros [sender receiver payload spectator] s' H.
  simpl in H. destruct sender; try discriminate.
  inversion H; subst s'; split; reflexivity.
Qed.

Theorem fsem02CloseOwnerNoReplay :
  forall s senderHalf final,
    fsem02CloseSender s = Some senderHalf ->
    fsem02CloseReceiver senderHalf = Some final ->
    fsem02CloseSender final = None /\
    fsem02CloseReceiver final = None.
Proof.
  intros [sender receiver payload spectator] senderHalf final Hsender Hreceiver.
  simpl in Hsender. destruct sender; try discriminate.
  inversion Hsender; subst senderHalf; clear Hsender.
  simpl in Hreceiver. destruct receiver; try discriminate.
  inversion Hreceiver; subst final; clear Hreceiver.
  split; reflexivity.
Qed.
