From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import
  FSEM02PingAdaptiveDualHeadDualResourceLadder
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingAdaptiveHeadResourcePriorityRetry
  FSEM02PingAdaptiveFreePeerResourceShapeRetry
  FSEM02PingMixedPrefixFault.

(* Non-normative FSEM-02: four independently repaired external observation
   sites. Boolean repair flags are test inputs, not source authority.
   Finite nat-carrier semantics are not native Haskell Map/Set refinement. *)
Definition fsem02FourRepairMaskGate
  (client server ec es badClient badServer : nat)
  (badClientResource badServerResource : fsem02AdaptiveResourceShape)
  (repairClientHead repairServerHead repairClientResource repairServerResource : bool)
  (before : fsem02MixPhaseMap) : fsem02AdaptiveHeadShapeResult :=
  fsem02AdaptiveHeadShapeGate client server ec es
    (if repairClientHead then ec else badClient)
    (if repairServerHead then es else badServer)
    (if repairClientResource then FSEM02EndpointResource ec else badClientResource)
    (if repairServerResource then FSEM02EndpointResource es else badServerResource)
    before.

(* One law classifies all 16 masks: the first unrepaired site wins,
   even when sites are restored in a different order. *)
Theorem fsem02FourRepairMaskExactPriority :
  forall client server ec es badClient badServer
         badClientResource badServerResource clientFault serverFault before
         repairClientHead repairServerHead repairClientResource repairServerResource,
    ec <> badClient -> es <> badServer ->
    fsem02AdaptiveResourceShapeCheck ec badClientResource = Some clientFault ->
    fsem02AdaptiveResourceShapeCheck es badServerResource = Some serverFault ->
    fsem02FourRepairMaskGate client server ec es badClient badServer
      badClientResource badServerResource
      repairClientHead repairServerHead repairClientResource repairServerResource before =
      if repairClientHead then
        if repairServerHead then
          if repairClientResource then
            if repairServerResource then
              FSEM02HeadShapeStep (fsem02AdaptivePhaseJointPing client server before)
            else FSEM02ShapeMismatch server serverFault
          else FSEM02ShapeMismatch client clientFault
        else FSEM02HeadMismatch server es badServer
      else FSEM02HeadMismatch client ec badClient.
Proof.
  intros client server ec es badClient badServer
    badClientResource badServerResource clientFault serverFault before
    repairClientHead repairServerHead repairClientResource repairServerResource
    Hclient Hserver HresourceClient HresourceServer.
  apply Nat.eqb_neq in Hclient.
  apply Nat.eqb_neq in Hserver.
  unfold fsem02FourRepairMaskGate.
  destruct repairClientHead, repairServerHead,
    repairClientResource, repairServerResource;
    unfold fsem02AdaptiveHeadShapeGate, fsem02AdaptiveShapeGatedPing;
    simpl;
    repeat (rewrite Nat.eqb_refl || rewrite Hclient || rewrite Hserver ||
            rewrite HresourceClient || rewrite HresourceServer);
    reflexivity.
Qed.

(* No partially repaired state manufactures a successor. The all-true mask
   merely exposes the separately admitted joint phase transition. *)
Theorem fsem02IncompleteRepairMaskCannotStep :
  forall client server ec es badClient badServer
         badClientResource badServerResource clientFault serverFault before
         repairClientHead repairServerHead repairClientResource repairServerResource
         after,
    ec <> badClient -> es <> badServer ->
    fsem02AdaptiveResourceShapeCheck ec badClientResource = Some clientFault ->
    fsem02AdaptiveResourceShapeCheck es badServerResource = Some serverFault ->
    (repairClientHead && repairServerHead &&
     repairClientResource && repairServerResource)%bool = false ->
    fsem02FourRepairMaskGate client server ec es badClient badServer
      badClientResource badServerResource
      repairClientHead repairServerHead repairClientResource repairServerResource before
      <> FSEM02HeadShapeStep (Some after).
Proof.
  intros client server ec es badClient badServer
    badClientResource badServerResource clientFault serverFault before
    repairClientHead repairServerHead repairClientResource repairServerResource
    after Hclient Hserver HresourceClient HresourceServer Hincomplete.
  rewrite (fsem02FourRepairMaskExactPriority
    client server ec es badClient badServer
    badClientResource badServerResource clientFault serverFault before
    repairClientHead repairServerHead repairClientResource repairServerResource
    Hclient Hserver HresourceClient HresourceServer).
  destruct repairClientHead, repairServerHead,
    repairClientResource, repairServerResource;
    simpl in *; congruence.
Qed.

(* All four explicit restorations recover the already-authorized half-Close
   suffix, preserving the external choice/activation/disposal premises. *)
Theorem fsem02FourRepairsRecoverAuthorizedHalfClose :
  forall priorClient priorServer freeClient freeServer
         priorClientPhase priorServerPhase ec es
         badClient badServer badClientResource badServerResource before,
    freeClient <> priorClient -> freeClient <> priorServer ->
    freeServer <> priorClient -> freeServer <> priorServer ->
    before freeClient = FSEM02AwaitPing ->
    before freeServer = FSEM02AwaitPing ->
    let prefix := fsem02MixWrite priorClient priorClientPhase
       (fsem02MixWrite priorServer priorServerPhase before) in
    fsem02FourRepairMaskGate freeClient freeServer ec es badClient badServer
      badClientResource badServerResource true true true true prefix =
      FSEM02HeadShapeStep (Some (fsem02MixWrite freeServer FSEM02LiveEnd
        (fsem02MixWrite freeClient FSEM02LiveEnd prefix))).
Proof.
  intros priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase ec es badClient badServer
    badClientResource badServerResource before Hcc Hcs Hsc Hss Hc Hs.
  change (fsem02AdaptiveHeadShapeGate freeClient freeServer ec es ec es
    (FSEM02EndpointResource ec) (FSEM02EndpointResource es)
    (fsem02MixWrite priorClient priorClientPhase
       (fsem02MixWrite priorServer priorServerPhase before)) =
    FSEM02HeadShapeStep (Some
      (fsem02MixWrite freeServer FSEM02LiveEnd
        (fsem02MixWrite freeClient FSEM02LiveEnd
          (fsem02MixWrite priorClient priorClientPhase
             (fsem02MixWrite priorServer priorServerPhase before)))))).
  apply fsem02FourFaultFullyRepairedHalfClose; assumption.
Qed.
