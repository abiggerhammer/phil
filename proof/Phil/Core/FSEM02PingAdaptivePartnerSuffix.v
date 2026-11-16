From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Phil.Core Require Import FSEM02PingPartialPartnerPrefix.

(* FSEM-02 NON-NORMATIVE. Dual source-checked heads, activated participants,
   root/protocol/partner-selection authority, scheduler and disposal are
   external premises, never inferred from this nat->bool ledger. *)

Theorem fsem02AdaptiveTwoFreePartnerChoicesIndividuallyEnabled :
  forall consumedClient consumedServer freeClient optionServerA optionServerB before,
    freeClient <> consumedClient ->
    freeClient <> consumedServer ->
    optionServerA <> consumedClient ->
    optionServerA <> consumedServer ->
    optionServerB <> consumedClient ->
    optionServerB <> consumedServer ->
    freeClient <> optionServerA ->
    freeClient <> optionServerB ->
    before freeClient = false ->
    before optionServerA = false ->
    before optionServerB = false ->
    exists afterA afterB,
      fsem02MixedJointPing freeClient optionServerA
        (fsem02MixedPingMark consumedServer
          (fsem02MixedPingMark consumedClient before)) = Some afterA /\
      fsem02MixedJointPing freeClient optionServerB
        (fsem02MixedPingMark consumedServer
          (fsem02MixedPingMark consumedClient before)) = Some afterB.
Proof.
  intros consumedClient consumedServer freeClient optionServerA optionServerB
    before Hfc Hfs Has Hasa Hbs Hbsa _ _ Hfree Ha Hb.
  exists (fsem02MixedPingMark optionServerA
    (fsem02MixedPingMark freeClient
      (fsem02MixedPingMark consumedServer
        (fsem02MixedPingMark consumedClient before)))).
  exists (fsem02MixedPingMark optionServerB
    (fsem02MixedPingMark freeClient
      (fsem02MixedPingMark consumedServer
        (fsem02MixedPingMark consumedClient before)))).
  split.
  - apply fsem02MixedPingHealthyPairProducesBothSuccessors.
    + rewrite (fsem02MixedPingIndependentParticipantFrame
                 consumedClient consumedServer freeClient before Hfc Hfs).
      exact Hfree.
    + rewrite (fsem02MixedPingIndependentParticipantFrame
                 consumedClient consumedServer optionServerA before Has Hasa).
      exact Ha.
  - apply fsem02MixedPingHealthyPairProducesBothSuccessors.
    + rewrite (fsem02MixedPingIndependentParticipantFrame
                 consumedClient consumedServer freeClient before Hfc Hfs).
      exact Hfree.
    + rewrite (fsem02MixedPingIndependentParticipantFrame
                 consumedClient consumedServer optionServerB before Hbs Hbsa).
      exact Hb.
Qed.

Theorem fsem02AdaptiveFreeSpectatorNotConsumedByEitherChoice :
  forall freeClient serverA serverB spectator before,
    spectator <> freeClient ->
    spectator <> serverA ->
    spectator <> serverB ->
    fsem02MixedPingMark serverA (fsem02MixedPingMark freeClient before) spectator =
      before spectator /\
    fsem02MixedPingMark serverB (fsem02MixedPingMark freeClient before) spectator =
      before spectator.
Proof.
  intros freeClient serverA serverB spectator before Hc Ha Hb.
  split.
  - now apply fsem02MixedPingIndependentParticipantFrame.
  - now apply fsem02MixedPingIndependentParticipantFrame.
Qed.
