From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import
  FSEM02PingAdaptiveCrossPeerHeadResourceShapeRetry
  FSEM02PingAdaptiveCrossPeerHeadOwnerRetry
  FSEM02PingAdaptiveHeadResourcePriorityRetry
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingMixedPrefixFault.

(* FSEM-02, non-normative: two invalid projected heads plus an independently
   malformed endpoint resource. Finite nat carriers only. All nominal
   activation, partner, root, Close/disposal, scheduler and assurance
   authority, and native Haskell representation identity remain premises. *)

Theorem fsem02DualHeadClientWrongTypeLadder :
  forall client server ec es badClient badServer before,
    ec <> badClient -> es <> badServer ->
    fsem02AdaptiveHeadShapeGate client server ec es badClient badServer
      FSEM02NonEndpointResource (FSEM02EndpointResource es) before =
      FSEM02HeadMismatch client ec badClient /\
    fsem02AdaptiveHeadShapeGate client server ec es ec badServer
      FSEM02NonEndpointResource (FSEM02EndpointResource es) before =
      FSEM02HeadMismatch server es badServer /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      FSEM02NonEndpointResource (FSEM02EndpointResource es) before =
      FSEM02ShapeMismatch client FSEM02WrongResourceType.
Proof.
  intros client server ec es badClient badServer before Hc Hs.
  split.
  - apply fsem02AdaptiveClientBadHeadMasksResource; exact Hc.
  - split.
    + apply fsem02AdaptiveServerBadHeadMasksResource; exact Hs.
    + apply fsem02AdaptiveClientHeadRepairExposesWrongType.
Qed.

Theorem fsem02DualHeadClientWrongSessionLadder :
  forall client server ec es badClient badServer wrongResource before,
    ec <> badClient -> es <> badServer -> ec <> wrongResource ->
    fsem02AdaptiveHeadShapeGate client server ec es badClient badServer
      (FSEM02EndpointResource wrongResource) (FSEM02EndpointResource es) before =
      FSEM02HeadMismatch client ec badClient /\
    fsem02AdaptiveHeadShapeGate client server ec es ec badServer
      (FSEM02EndpointResource wrongResource) (FSEM02EndpointResource es) before =
      FSEM02HeadMismatch server es badServer /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource wrongResource) (FSEM02EndpointResource es) before =
      FSEM02ShapeMismatch client FSEM02WrongResourceSession.
Proof.
  intros client server ec es badClient badServer wrongResource before Hc Hs Hr.
  split.
  - apply fsem02AdaptiveClientBadHeadMasksResource; exact Hc.
  - split.
    + apply fsem02AdaptiveServerBadHeadMasksResource; exact Hs.
    + destruct (fsem02CrossPeerServerHeadClientWrongSessionLadder
        client server ec es badServer wrongResource before Hs Hr) as [_ Hshape].
      exact Hshape.
Qed.

Theorem fsem02DualHeadServerWrongTypeLadder :
  forall client server ec es badClient badServer before,
    ec <> badClient -> es <> badServer ->
    fsem02AdaptiveHeadShapeGate client server ec es badClient badServer
      (FSEM02EndpointResource ec) FSEM02NonEndpointResource before =
      FSEM02HeadMismatch client ec badClient /\
    fsem02AdaptiveHeadShapeGate client server ec es ec badServer
      (FSEM02EndpointResource ec) FSEM02NonEndpointResource before =
      FSEM02HeadMismatch server es badServer /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) FSEM02NonEndpointResource before =
      FSEM02ShapeMismatch server FSEM02WrongResourceType.
Proof.
  intros client server ec es badClient badServer before Hc Hs.
  split.
  - apply fsem02AdaptiveClientBadHeadMasksResource; exact Hc.
  - split.
    + apply fsem02AdaptiveServerBadHeadMasksResource; exact Hs.
    + destruct (fsem02CrossPeerClientHeadServerWrongTypeLadder
        client server ec es badClient before Hc) as [_ Hshape].
      exact Hshape.
Qed.

Theorem fsem02DualHeadServerWrongSessionLadder :
  forall client server ec es badClient badServer wrongResource before,
    ec <> badClient -> es <> badServer -> es <> wrongResource ->
    fsem02AdaptiveHeadShapeGate client server ec es badClient badServer
      (FSEM02EndpointResource ec) (FSEM02EndpointResource wrongResource) before =
      FSEM02HeadMismatch client ec badClient /\
    fsem02AdaptiveHeadShapeGate client server ec es ec badServer
      (FSEM02EndpointResource ec) (FSEM02EndpointResource wrongResource) before =
      FSEM02HeadMismatch server es badServer /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) (FSEM02EndpointResource wrongResource) before =
      FSEM02ShapeMismatch server FSEM02WrongResourceSession.
Proof.
  intros client server ec es badClient badServer wrongResource before Hc Hs Hr.
  split.
  - apply fsem02AdaptiveClientBadHeadMasksResource; exact Hc.
  - split.
    + apply fsem02AdaptiveServerBadHeadMasksResource; exact Hs.
    + destruct (fsem02CrossPeerClientHeadServerWrongSessionLadder
        client server ec es badClient wrongResource before Hc Hr) as [_ Hshape].
      exact Hshape.
Qed.

(* Only explicit repair of both heads and the resource permits the
   externally authorized phase-map suffix. No Haskell refinement is claimed. *)
Theorem fsem02DualHeadResourceFullyRepairedHalfClose :
  forall priorClient priorServer freeClient freeServer
         priorClientPhase priorServerPhase ec es before,
    freeClient <> priorClient -> freeClient <> priorServer ->
    freeServer <> priorClient -> freeServer <> priorServer ->
    before freeClient = FSEM02AwaitPing ->
    before freeServer = FSEM02AwaitPing ->
    let prefix := fsem02MixWrite priorClient priorClientPhase
      (fsem02MixWrite priorServer priorServerPhase before) in
    fsem02AdaptiveHeadShapeGate freeClient freeServer ec es ec es
      (FSEM02EndpointResource ec) (FSEM02EndpointResource es) prefix =
      FSEM02HeadShapeStep (Some (fsem02MixWrite freeServer FSEM02LiveEnd
        (fsem02MixWrite freeClient FSEM02LiveEnd prefix))).
Proof.
  intros priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase ec es before
    Hcc Hcs Hsc Hss Hc Hs.
  exact (fsem02CrossPeerShapeBothRepairedHalfClose
    priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase ec es before
    Hcc Hcs Hsc Hss Hc Hs).
Qed.
