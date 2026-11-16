From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Phil.Core Require Import FSEM02PingMixedPrefixFault FSEM02PingAdaptivePartnerSuffix.

(* FSEM-02 NON-NORMATIVE finite phase abstraction. A nat key denotes a
   participant, NOT a native ProcessKey. A legal pair, selected root, protocol
   instance/role, typed source witness, initial activation and each local
   terminal Close authorization remain explicit external premises. *)

Definition fsem02AdaptivePhaseJointPing
  (client server : nat) (before : fsem02MixPhaseMap)
  : option fsem02MixPhaseMap :=
  match before client, before server with
  | FSEM02AwaitPing, FSEM02AwaitPing =>
      Some (fsem02MixWrite server FSEM02LiveEnd
              (fsem02MixWrite client FSEM02LiveEnd before))
  | _, _ => None
  end.

Theorem fsem02AdaptiveHalfClosedFreePairStillEnabled :
  forall priorClient priorServer freeClient freeServer
         phaseClient phaseServer before,
    freeClient <> priorClient -> freeClient <> priorServer ->
    freeServer <> priorClient -> freeServer <> priorServer ->
    before freeClient = FSEM02AwaitPing ->
    before freeServer = FSEM02AwaitPing ->
    fsem02AdaptivePhaseJointPing freeClient freeServer
      (fsem02MixWrite priorClient phaseClient
        (fsem02MixWrite priorServer phaseServer before)) =
      Some (fsem02MixWrite freeServer FSEM02LiveEnd
        (fsem02MixWrite freeClient FSEM02LiveEnd
          (fsem02MixWrite priorClient phaseClient
            (fsem02MixWrite priorServer phaseServer before)))).
Proof.
  intros priorClient priorServer freeClient freeServer
    phaseClient phaseServer before Hcc Hcs Hsc Hss Hc Hs.
  unfold fsem02AdaptivePhaseJointPing.
  rewrite (fsem02MixedPrefixIndependentSiteFrame
             priorClient freeClient phaseClient
             (fsem02MixWrite priorServer phaseServer before) Hcc).
  rewrite (fsem02MixedPrefixIndependentSiteFrame
             priorServer freeClient phaseServer before Hcs).
  rewrite (fsem02MixedPrefixIndependentSiteFrame
             priorClient freeServer phaseClient
             (fsem02MixWrite priorServer phaseServer before) Hsc).
  rewrite (fsem02MixedPrefixIndependentSiteFrame
             priorServer freeServer phaseServer before Hss).
  now rewrite Hc, Hs.
Qed.

Theorem fsem02AdaptiveRetiredClientCannotRematch :
  forall client server before,
    fsem02AdaptivePhaseJointPing client server
      (fsem02MixWrite client FSEM02Retired before) = None.
Proof.
  intros client server before.
  unfold fsem02AdaptivePhaseJointPing, fsem02MixWrite.
  now rewrite Nat.eqb_refl.
Qed.

Theorem fsem02AdaptiveCommittedServerCannotRematch :
  forall client server before,
    fsem02AdaptivePhaseJointPing client server
      (fsem02MixWrite server FSEM02LiveEnd before) = None.
Proof.
  intros client server before.
  unfold fsem02AdaptivePhaseJointPing, fsem02MixWrite.
  rewrite Nat.eqb_refl.
  destruct (if Nat.eqb client server then FSEM02LiveEnd else before client);
    reflexivity.
Qed.

Theorem fsem02AdaptiveHalfCloseSpectatorFrame :
  forall priorClient priorServer spectator
         phaseClient phaseServer before,
    spectator <> priorClient -> spectator <> priorServer ->
    fsem02MixWrite priorClient phaseClient
      (fsem02MixWrite priorServer phaseServer before) spectator =
      before spectator.
Proof.
  intros priorClient priorServer spectator
    phaseClient phaseServer before Hc Hs.
  rewrite (fsem02MixedPrefixIndependentSiteFrame
             priorClient spectator phaseClient
             (fsem02MixWrite priorServer phaseServer before) Hc).
  now apply fsem02MixedPrefixIndependentSiteFrame.
Qed.
