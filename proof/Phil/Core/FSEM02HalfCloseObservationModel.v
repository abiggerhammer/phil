From Stdlib Require Import Lists.List Bool.Bool.
From Phil.Core Require Import FSEM02CloseOrderObservationModel.

(* NON-NORMATIVE half-Close finite owner-bit model. The live flags stand for
   externally admitted distinct endpoint occurrences, not Haskell maps or
   source-derived terminal authority. *)
Inductive FSEM02HalfCloseTag :=
| FSEM02SenderHalfReplayRefused
| FSEM02SenderPeerClosed
| FSEM02ReceiverHalfReplayRefused
| FSEM02ReceiverPeerClosed.

Definition fsem02HalfCloseCommitted (tag : FSEM02HalfCloseTag) : bool :=
  match tag with
  | FSEM02SenderPeerClosed | FSEM02ReceiverPeerClosed => true
  | FSEM02SenderHalfReplayRefused | FSEM02ReceiverHalfReplayRefused => false
  end.

Theorem fsem02SenderHalfCannotReplay :
  forall s half,
    fsem02CloseSender s = Some half ->
    fsem02CloseSender half = None.
Proof.
  intros [sender receiver payload spectator] half H.
  simpl in H. destruct sender; try discriminate.
  inversion H; subst half; reflexivity.
Qed.

Theorem fsem02ReceiverHalfCannotReplay :
  forall s half,
    fsem02CloseReceiver s = Some half ->
    fsem02CloseReceiver half = None.
Proof.
  intros [sender receiver payload spectator] half H.
  simpl in H. destruct receiver; try discriminate.
  inversion H; subst half; reflexivity.
Qed.

Theorem fsem02SenderHalfPermitsLivePeer :
  forall s half,
    fsem02CloseSender s = Some half ->
    fsem02ReceiverLive s = true ->
    exists final,
      fsem02CloseReceiver half = Some final /\
      fsem02SenderLive final = false /\
      fsem02ReceiverLive final = false /\
      fsem02PayloadPresent final = fsem02PayloadPresent s /\
      fsem02SpectatorPresent final = fsem02SpectatorPresent s.
Proof.
  intros [sender receiver payload spectator] half Hsender Hreceiver.
  simpl in Hsender, Hreceiver.
  destruct sender; try discriminate.
  destruct receiver; try discriminate.
  inversion Hsender; subst half.
  exists {| fsem02SenderLive := false; fsem02ReceiverLive := false;
            fsem02PayloadPresent := payload;
            fsem02SpectatorPresent := spectator |}.
  repeat split; reflexivity.
Qed.

Theorem fsem02ReceiverHalfPermitsLivePeer :
  forall s half,
    fsem02CloseReceiver s = Some half ->
    fsem02SenderLive s = true ->
    exists final,
      fsem02CloseSender half = Some final /\
      fsem02SenderLive final = false /\
      fsem02ReceiverLive final = false /\
      fsem02PayloadPresent final = fsem02PayloadPresent s /\
      fsem02SpectatorPresent final = fsem02SpectatorPresent s.
Proof.
  intros [sender receiver payload spectator] half Hreceiver Hsender.
  simpl in Hsender, Hreceiver.
  destruct receiver; try discriminate.
  destruct sender; try discriminate.
  inversion Hreceiver; subst half.
  exists {| fsem02SenderLive := false; fsem02ReceiverLive := false;
            fsem02PayloadPresent := payload;
            fsem02SpectatorPresent := spectator |}.
  repeat split; reflexivity.
Qed.
