From Stdlib Require Import Lists.List.
From Phil.Core Require Import FSEM02TerminalObservationModel.
Import ListNotations.
(* Terminal OBS-V1; actual source/Core observation, bounded. *)
Definition fsem02TerminalObservedEvents : list FSEM02TerminalObservationTag :=
  [FSEM02WrongTerminalOutcomeRefused; FSEM02TerminalClosed; FSEM02TerminalReplayRefused].
