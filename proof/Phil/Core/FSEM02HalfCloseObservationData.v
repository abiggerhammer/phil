From Stdlib Require Import Lists.List.
From Phil.Core Require Import FSEM02HalfCloseObservationModel.
Import ListNotations.
(* Half-close OBS-V1; checked finite Haskell source/Core observation. *)
Definition fsem02HalfCloseObservedEvents : list FSEM02HalfCloseTag :=
  [FSEM02SenderHalfReplayRefused; FSEM02SenderPeerClosed; FSEM02ReceiverHalfReplayRefused; FSEM02ReceiverPeerClosed].
