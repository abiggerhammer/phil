From Stdlib Require Import Lists.List Bool.Bool.
From Phil.Core Require Import
  FSEM02RestrictedSourceObservationModel FSEM02RestrictedSourceObservationData.
Import ListNotations.

(* Independently compiled Rocq facts about the exact OBS-V1 data. The
   production checker-to-wire projection is checked by the strict Haskell
   regression and byte-for-byte CI comparison, not by this proof. *)
Theorem fsem02ObservedExactVerdicts :
  map fsem02ObservationCommitted fsem02ObservedEvents =
    [true; false; false; false; false].
Proof. reflexivity. Qed.

Theorem fsem02ObservedEveryRefusalHasNoCommittedEvent :
  map fsem02ObservationRefused (tl fsem02ObservedEvents) =
    [true; true; true; true].
Proof. reflexivity. Qed.

Theorem fsem02ObservedSourceErrorPriority :
  fsem02ObservedEvents =
    [FSEM02TransferCommitted;
     FSEM02SenderCloseRefused;
     FSEM02ReceiverCloseRefused;
     FSEM02SenderCloseRefused;
     FSEM02StaleReplayRefused].
Proof. reflexivity. Qed.

Theorem fsem02ObservedNoSecondTransfer :
  length (filter fsem02ObservationCommitted fsem02ObservedEvents) = 1.
Proof. reflexivity. Qed.
