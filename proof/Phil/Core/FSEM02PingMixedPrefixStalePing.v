From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(* FSEM-02, non-normative joint-Ping replay abstraction for three externally
   activated source-checked pairs. Each nat key represents a participant,
   while the boolean records whether that participant's predecessor has
   already been consumed by a successful atomic Ping. The model does not
   encode native ProcessKey/Session representations, grant role/instance
   authority, or prove native Haskell-to-Rocq refinement. *)

Definition fsem02MixedPingLedger : Type := nat -> bool.

Definition fsem02MixedPingMark
  (site : nat) (before : fsem02MixedPingLedger)
  : fsem02MixedPingLedger :=
  fun key => if Nat.eqb key site then true else before key.

Definition fsem02MixedJointPing
  (client server : nat) (before : fsem02MixedPingLedger)
  : option fsem02MixedPingLedger :=
  if orb (before client) (before server) then None
  else Some (fsem02MixedPingMark server
               (fsem02MixedPingMark client before)).

Theorem fsem02MixedPingHealthyPairProducesBothSuccessors :
  forall client server before,
    before client = false -> before server = false ->
    fsem02MixedJointPing client server before =
      Some (fsem02MixedPingMark server
              (fsem02MixedPingMark client before)).
Proof.
  intros client server before Hc Hs.
  unfold fsem02MixedJointPing. now rewrite Hc, Hs.
Qed.

Theorem fsem02MixedPingConsumedClientRefusesExactReplay :
  forall client server before, before client = true ->
    fsem02MixedJointPing client server before = None.
Proof.
  intros client server before Hc.
  unfold fsem02MixedJointPing. now rewrite Hc.
Qed.

Theorem fsem02MixedPingConsumedServerRefusesExactReplay :
  forall client server before, before server = true ->
    fsem02MixedJointPing client server before = None.
Proof.
  intros client server before Hs.
  unfold fsem02MixedJointPing. rewrite Hs.
  destruct (before client); reflexivity.
Qed.

Theorem fsem02MixedPingPairConsumptionIsAtomic :
  forall client server before, client <> server ->
    fsem02MixedPingMark server (fsem02MixedPingMark client before) client = true /\
    fsem02MixedPingMark server (fsem02MixedPingMark client before) server = true.
Proof.
  intros client server before Hneq.
  unfold fsem02MixedPingMark.
  assert (Nat.eqb client server = false) as Hcs.
  { apply Nat.eqb_neq; exact Hneq. }
  split.
  - now rewrite Hcs, Nat.eqb_refl.
  - now rewrite Nat.eqb_refl.
Qed.

Theorem fsem02MixedPingAlreadyConsumedPairCannotRestart :
  forall client server before, client <> server ->
    fsem02MixedJointPing client server
      (fsem02MixedPingMark server
        (fsem02MixedPingMark client before)) = None.
Proof.
  intros client server before Hneq.
  unfold fsem02MixedJointPing, fsem02MixedPingMark.
  assert (Nat.eqb client server = false) as Hcs.
  { apply Nat.eqb_neq; exact Hneq. }
  now rewrite Hcs, Nat.eqb_refl.
Qed.

Theorem fsem02MixedPingIndependentParticipantFrame :
  forall client server spectator before,
    spectator <> client -> spectator <> server ->
    fsem02MixedPingMark server
      (fsem02MixedPingMark client before) spectator = before spectator.
Proof.
  intros client server spectator before Hclient Hserver.
  unfold fsem02MixedPingMark.
  apply Nat.eqb_neq in Hclient.
  apply Nat.eqb_neq in Hserver.
  now rewrite Hserver, Hclient.
Qed.
