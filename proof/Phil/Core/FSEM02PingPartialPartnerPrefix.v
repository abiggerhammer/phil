From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Phil.Core Require Import FSEM02PingPartnerSelection.

(* FSEM-02, NON-NORMATIVE: source-checked dual heads and the right to choose
   distinct participants are explicit premises. A finite nat->bool ledger is
   not an extracted representation of native ProcessKey or resource contexts. *)

Theorem fsem02PartialPartnerUntouchedPairStillAvailable :
  forall chosenClient chosenServer freeClient freeServer before,
    freeClient <> chosenClient ->
    freeClient <> chosenServer ->
    freeServer <> chosenClient ->
    freeServer <> chosenServer ->
    before freeClient = false -> before freeServer = false ->
    fsem02MixedJointPing freeClient freeServer
      (fsem02MixedPingMark chosenServer
        (fsem02MixedPingMark chosenClient before)) =
      Some (fsem02MixedPingMark freeServer
        (fsem02MixedPingMark freeClient
          (fsem02MixedPingMark chosenServer
            (fsem02MixedPingMark chosenClient before)))).
Proof.
  intros chosenClient chosenServer freeClient freeServer before
    Hcc Hcs Hsc Hss HfreeClient HfreeServer.
  apply fsem02MixedPingHealthyPairProducesBothSuccessors.
  - rewrite (fsem02MixedPingIndependentParticipantFrame
               chosenClient chosenServer freeClient before Hcc Hcs).
    exact HfreeClient.
  - rewrite (fsem02MixedPingIndependentParticipantFrame
               chosenClient chosenServer freeServer before Hsc Hss).
    exact HfreeServer.
Qed.

Theorem fsem02PartialPartnerSpentClientStillRefusesAfterDisjointPing :
  forall spentClient spentServer otherClient otherServer freeServer before,
    spentClient <> spentServer ->
    spentClient <> otherClient -> spentClient <> otherServer ->
    fsem02MixedJointPing spentClient freeServer
      (fsem02MixedPingMark otherServer
        (fsem02MixedPingMark otherClient
          (fsem02MixedPingMark spentServer
            (fsem02MixedPingMark spentClient before)))) = None.
Proof.
  intros spentClient spentServer otherClient otherServer freeServer before
    Hpair HotherClient HotherServer.
  apply fsem02MixedPingConsumedClientRefusesExactReplay.
  rewrite (fsem02MixedPingIndependentParticipantFrame
             otherClient otherServer spentClient
             (fsem02MixedPingMark spentServer
               (fsem02MixedPingMark spentClient before))
             HotherClient HotherServer).
  pose proof (fsem02MixedPingPairConsumptionIsAtomic
                spentClient spentServer before Hpair) as [Hspent _].
  exact Hspent.
Qed.

Theorem fsem02PartialPartnerSpentServerStillRefusesAfterDisjointPing :
  forall spentClient spentServer otherClient otherServer freeClient before,
    spentClient <> spentServer ->
    spentServer <> otherClient -> spentServer <> otherServer ->
    fsem02MixedJointPing freeClient spentServer
      (fsem02MixedPingMark otherServer
        (fsem02MixedPingMark otherClient
          (fsem02MixedPingMark spentServer
            (fsem02MixedPingMark spentClient before)))) = None.
Proof.
  intros spentClient spentServer otherClient otherServer freeClient before
    Hpair HotherClient HotherServer.
  apply fsem02MixedPingConsumedServerRefusesExactReplay.
  rewrite (fsem02MixedPingIndependentParticipantFrame
             otherClient otherServer spentServer
             (fsem02MixedPingMark spentServer
               (fsem02MixedPingMark spentClient before))
             HotherClient HotherServer).
  pose proof (fsem02MixedPingPairConsumptionIsAtomic
                spentClient spentServer before Hpair) as [_ Hspent].
  exact Hspent.
Qed.
