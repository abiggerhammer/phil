From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Phil.Core Require Import FSEM02PingMixedPrefixStalePing.

(* FSEM-02, non-normative. Partner selection is an EXTERNAL input: nat keys
   represent independently activated participants, not native ProcessKeys or
   an authority to select another participant. Equal role/instance and dual
   source-checked session heads are premises of the executable Haskell trace. *)

Theorem fsem02PartnerChoiceHealthyAlternative :
  forall client alternateServer before,
    before client = false -> before alternateServer = false ->
    fsem02MixedJointPing client alternateServer before =
      Some (fsem02MixedPingMark alternateServer
              (fsem02MixedPingMark client before)).
Proof.
  intros client alternateServer before Hc Hs.
  now apply fsem02MixedPingHealthyPairProducesBothSuccessors.
Qed.

Theorem fsem02PartnerChoiceSelectedClientCannotRematch :
  forall client selectedServer alternateServer before,
    client <> selectedServer ->
    fsem02MixedJointPing client alternateServer
      (fsem02MixedPingMark selectedServer
        (fsem02MixedPingMark client before)) = None.
Proof.
  intros client selectedServer alternateServer before Hdistinct.
  apply fsem02MixedPingConsumedClientRefusesExactReplay.
  pose proof (fsem02MixedPingPairConsumptionIsAtomic
                client selectedServer before Hdistinct) as [Hclient _].
  exact Hclient.
Qed.

Theorem fsem02PartnerChoiceSelectedServerCannotRematch :
  forall selectedClient selectedServer alternateClient before,
    selectedClient <> selectedServer ->
    fsem02MixedJointPing alternateClient selectedServer
      (fsem02MixedPingMark selectedServer
        (fsem02MixedPingMark selectedClient before)) = None.
Proof.
  intros selectedClient selectedServer alternateClient before Hdistinct.
  apply fsem02MixedPingConsumedServerRefusesExactReplay.
  pose proof (fsem02MixedPingPairConsumptionIsAtomic
                selectedClient selectedServer before Hdistinct) as [_ Hserver].
  exact Hserver.
Qed.

Theorem fsem02PartnerChoiceOtherParticipantUnchanged :
  forall client selectedServer other before,
    other <> client -> other <> selectedServer ->
    fsem02MixedPingMark selectedServer
      (fsem02MixedPingMark client before) other = before other.
Proof.
  intros client selectedServer other before Hc Hs.
  now apply fsem02MixedPingIndependentParticipantFrame.
Qed.
