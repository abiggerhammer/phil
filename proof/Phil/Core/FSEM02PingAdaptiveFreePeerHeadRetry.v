From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import FSEM02PingAdaptiveHalfCloseSuffix.

(* FSEM-02, non-normative finite phase bridge. Deliberately injected End
   on a still-free peer does not make a source-checked Ping admissible.
   The repaired input is a NEW external state, not an implicit rollback.
   ProcessKey, instance/role, activation and partner authorization are not
   encoded by these nat phase keys. *)
Theorem fsem02AdaptivePoisonedFreeClientRefuses :
  forall client server before,
    fsem02AdaptivePhaseJointPing client server
      (fsem02MixWrite client FSEM02LiveEnd before) = None.
Proof.
  intros client server before.
  unfold fsem02AdaptivePhaseJointPing, fsem02MixWrite.
  now rewrite Nat.eqb_refl.
Qed.

Theorem fsem02AdaptivePoisonedFreeServerRefuses :
  forall client server before,
    fsem02AdaptivePhaseJointPing client server
      (fsem02MixWrite server FSEM02LiveEnd before) = None.
Proof.
  exact fsem02AdaptiveCommittedServerCannotRematch.
Qed.

Theorem fsem02AdaptiveHalfCloseFreePeerFaultsThenExactRetry :
  forall priorClient priorServer freeClient freeServer phaseClient phaseServer before,
    freeClient <> priorClient -> freeClient <> priorServer ->
    freeServer <> priorClient -> freeServer <> priorServer ->
    freeClient <> freeServer ->
    before freeClient = FSEM02AwaitPing ->
    before freeServer = FSEM02AwaitPing ->
    let prefix :=
      fsem02MixWrite priorClient phaseClient
        (fsem02MixWrite priorServer phaseServer before) in
    fsem02AdaptivePhaseJointPing freeClient freeServer
      (fsem02MixWrite freeClient FSEM02LiveEnd prefix) = None /\
    fsem02AdaptivePhaseJointPing freeClient freeServer
      (fsem02MixWrite freeServer FSEM02LiveEnd prefix) = None /\
    fsem02AdaptivePhaseJointPing freeClient freeServer prefix =
      Some (fsem02MixWrite freeServer FSEM02LiveEnd
        (fsem02MixWrite freeClient FSEM02LiveEnd prefix)).
Proof.
  intros priorClient priorServer freeClient freeServer
    phaseClient phaseServer before Hcc Hcs Hsc Hss _ Hc Hs.
  simpl.
  split.
  - apply fsem02AdaptivePoisonedFreeClientRefuses.
  - split.
    + apply fsem02AdaptivePoisonedFreeServerRefuses.
    + apply fsem02AdaptiveHalfClosedFreePairStillEnabled; assumption.
Qed.

Theorem fsem02AdaptiveFaultInjectionLeavesUnrelatedPhaseUntouched :
  forall site spectator before,
    site <> spectator ->
    fsem02MixWrite site FSEM02LiveEnd before spectator =
      before spectator.
Proof.
  intros site spectator before Hneq.
  now apply fsem02MixedPrefixIndependentSiteFrame.
Qed.
