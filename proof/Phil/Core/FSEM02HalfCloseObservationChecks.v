From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From Phil.Core Require Import FSEM02HalfCloseObservationModel FSEM02HalfCloseObservationData.
Import ListNotations.

(* These are checks over a finite Haskell-produced datum. No universal native
   state-to-model simulation or source authority follows from matching tags. *)
Theorem fsem02HalfCloseExactObservation :
  fsem02HalfCloseObservedEvents =
    [FSEM02SenderHalfReplayRefused; FSEM02SenderPeerClosed;
     FSEM02ReceiverHalfReplayRefused; FSEM02ReceiverPeerClosed].
Proof. reflexivity. Qed.

Theorem fsem02HalfCloseSenderPair :
  firstn 2 fsem02HalfCloseObservedEvents =
    [FSEM02SenderHalfReplayRefused; FSEM02SenderPeerClosed].
Proof. reflexivity. Qed.

Theorem fsem02HalfCloseReceiverPair :
  skipn 2 fsem02HalfCloseObservedEvents =
    [FSEM02ReceiverHalfReplayRefused; FSEM02ReceiverPeerClosed].
Proof. reflexivity. Qed.

Theorem fsem02HalfCloseTwoFiniteCommitments :
  length (filter fsem02HalfCloseCommitted fsem02HalfCloseObservedEvents) = 2.
Proof. reflexivity. Qed.

Theorem fsem02HalfCloseRetriesAreNotCommits :
  fsem02HalfCloseCommitted
    (nth 0 fsem02HalfCloseObservedEvents FSEM02SenderHalfReplayRefused) = false /\
  fsem02HalfCloseCommitted
    (nth 2 fsem02HalfCloseObservedEvents FSEM02ReceiverHalfReplayRefused) = false.
Proof. split; reflexivity. Qed.
