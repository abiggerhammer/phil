From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import
  FSEM02PingAdaptiveHeadResourcePriorityRetry
  FSEM02PingAdaptiveFreePeerResourceShapeRetry
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingMixedPrefixFault.

(* FSEM-02, non-normative. Both projected session heads are checked before
   either independent linear-owner resource observation. Model identities
   are nat carriers; actual source/process keys, external matching, root,
   activation, scheduling, Close/disposal and assurance are NOT derived by
   this model. This is not a native-Haskell refinement theorem. *)

Theorem fsem02CrossPeerClientHeadMasksMissingServer :
  forall client server ec es observed before,
    ec <> observed ->
    fsem02AdaptiveHeadShapeGate client server ec es observed es
      (FSEM02EndpointResource ec) FSEM02NoResource before =
      FSEM02HeadMismatch client ec observed.
Proof.
  intros client server ec es observed before Hneq.
  unfold fsem02AdaptiveHeadShapeGate.
  assert (Hbad : Nat.eqb ec observed = false).
  { apply Nat.eqb_neq; exact Hneq. }
  now rewrite Hbad.
Qed.

Theorem fsem02CrossPeerServerHeadMasksMissingClient :
  forall client server ec es observed before,
    es <> observed ->
    fsem02AdaptiveHeadShapeGate client server ec es ec observed
      FSEM02NoResource (FSEM02EndpointResource es) before =
      FSEM02HeadMismatch server es observed.
Proof.
  intros client server ec es observed before Hneq.
  unfold fsem02AdaptiveHeadShapeGate.
  assert (Hbad : Nat.eqb es observed = false).
  { apply Nat.eqb_neq; exact Hneq. }
  now rewrite Nat.eqb_refl, Hbad.
Qed.

Theorem fsem02CrossPeerClientRepairExposesServerMissing :
  forall client server ec es before,
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) FSEM02NoResource before =
      FSEM02ShapeMismatch server FSEM02MissingOwner.
Proof.
  intros.
  unfold fsem02AdaptiveHeadShapeGate, fsem02AdaptiveShapeGatedPing,
    fsem02AdaptiveResourceShapeCheck.
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem fsem02CrossPeerServerRepairExposesClientMissing :
  forall client server ec es before,
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      FSEM02NoResource (FSEM02EndpointResource es) before =
      FSEM02ShapeMismatch client FSEM02MissingOwner.
Proof.
  intros.
  unfold fsem02AdaptiveHeadShapeGate, fsem02AdaptiveShapeGatedPing,
    fsem02AdaptiveResourceShapeCheck.
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(* If BOTH projected heads are bad, Client wins. Repairing just Client
   reveals the Server error, rather than committing any partial successor. *)
Theorem fsem02CrossPeerTwoBadHeadsRepairOrder :
  forall client server ec es badClient badServer rc rs before,
    ec <> badClient -> es <> badServer ->
    fsem02AdaptiveHeadShapeGate client server ec es badClient badServer
      rc rs before = FSEM02HeadMismatch client ec badClient /\
    fsem02AdaptiveHeadShapeGate client server ec es ec badServer
      rc rs before = FSEM02HeadMismatch server es badServer.
Proof.
  intros client server ec es badClient badServer rc rs before Hc Hs.
  assert (HbadC : Nat.eqb ec badClient = false).
  { apply Nat.eqb_neq; exact Hc. }
  assert (HbadS : Nat.eqb es badServer = false).
  { apply Nat.eqb_neq; exact Hs. }
  split; unfold fsem02AdaptiveHeadShapeGate.
  - now rewrite HbadC.
  - now rewrite Nat.eqb_refl, HbadS.
Qed.

(* Exact repaired after-prefix execution is still conditional on the
   pre-existing phase-map premises and externally authorized pairing. *)
Theorem fsem02CrossPeerHalfCloseFullyRepaired :
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
  exact (fsem02AdaptiveHalfCloseCombinedRepair
    priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase ec es before
    Hcc Hcs Hsc Hss Hc Hs).
Qed.
