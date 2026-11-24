From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From Phil.Core Require Import FSEM02CloseOrderObservationModel FSEM02CloseOrderObservationData.
Import ListNotations.

(* Finite event facts only; external authority, Haskell producer fidelity,
   state identities and the general SessionStep/Concurrency semantics remain
   separate premises rather than theorems of this wire. *)
Theorem fsem02CloseOrderExactObservedEvents :
  fsem02CloseOrderObservedEvents =
    [FSEM02SenderFirstConverged; FSEM02ReceiverFirstConverged;
     FSEM02StaleEndpointRefused; FSEM02StaleEndpointRefused;
     FSEM02StaleEndpointRefused; FSEM02StaleEndpointRefused].
Proof. reflexivity. Qed.

Theorem fsem02CloseOrderAcceptedPrefix :
  firstn 2 fsem02CloseOrderObservedEvents =
    [FSEM02SenderFirstConverged; FSEM02ReceiverFirstConverged].
Proof. reflexivity. Qed.

Theorem fsem02CloseOrderRefusedSuffix :
  skipn 2 fsem02CloseOrderObservedEvents =
    repeat FSEM02StaleEndpointRefused 4.
Proof. reflexivity. Qed.

Theorem fsem02CloseOrderTwoFiniteConvergences :
  length (filter fsem02CloseOrderConverged fsem02CloseOrderObservedEvents) = 2.
Proof. reflexivity. Qed.

Theorem fsem02CloseOrderNoFiniteReplayCommit :
  forall tag,
    In tag (skipn 2 fsem02CloseOrderObservedEvents) ->
    fsem02CloseOrderConverged tag = false.
Proof.
  intros tag Hin.
  simpl in Hin.
  destruct Hin as [Heq | [Heq | [Heq | [Heq | Hnil]]]];
    try contradiction; subst; reflexivity.
Qed.
