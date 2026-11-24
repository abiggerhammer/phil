From Stdlib Require Import Lists.List.
From Phil.Core Require Import FSEM02CloseOrderObservationModel.
Import ListNotations.
(* Close-order OBS-V1; checked finite Haskell source/Core observation. *)
Definition fsem02CloseOrderObservedEvents : list FSEM02CloseOrderTag :=
  [FSEM02SenderFirstConverged; FSEM02ReceiverFirstConverged; FSEM02StaleEndpointRefused; FSEM02StaleEndpointRefused; FSEM02StaleEndpointRefused; FSEM02StaleEndpointRefused].
