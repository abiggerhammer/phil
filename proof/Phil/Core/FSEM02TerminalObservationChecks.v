From Stdlib Require Import Lists.List Bool.Bool.
From Phil.Core Require Import
  FSEM02RestrictedSourceObservationModel FSEM02RestrictedSourceObservationData
  FSEM02TerminalObservationModel FSEM02TerminalObservationData.
Import ListNotations.

(* Checked finite datum with source/Core emitter equality tested separately;
   the producer-to-Rocq correspondence remains explicitly conditional. *)
Theorem fsem02TerminalObservedExactOrder :
  fsem02TerminalObservedEvents =
    [FSEM02WrongTerminalOutcomeRefused;
     FSEM02TerminalClosed;
     FSEM02TerminalReplayRefused].
Proof. reflexivity. Qed.

Theorem fsem02TerminalObservedOneClose :
  length (filter fsem02TerminalCommitted fsem02TerminalObservedEvents) = 1.
Proof. reflexivity. Qed.

Theorem fsem02TerminalObservedRefusalSequence :
  map fsem02TerminalRefused fsem02TerminalObservedEvents =
    [true; false; true].
Proof. reflexivity. Qed.

Theorem fsem02TerminalNoSecondClose :
  filter fsem02TerminalCommitted (tl (tl fsem02TerminalObservedEvents)) = [].
Proof. reflexivity. Qed.

Theorem fsem02TerminalRetainsSinglePriorPayloadTransfer :
  length (filter fsem02ObservationCommitted fsem02ObservedEvents) = 1 /\
  length (filter fsem02TerminalCommitted fsem02TerminalObservedEvents) = 1.
Proof. split; reflexivity. Qed.
