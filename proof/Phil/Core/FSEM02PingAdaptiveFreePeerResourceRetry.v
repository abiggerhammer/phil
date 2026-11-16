From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import FSEM02PingAdaptiveHalfCloseSuffix FSEM02PingAdaptiveFreePeerHeadRetry.

(* FSEM-02: bounded non-normative resource gate around an already-admitted
   adaptive Ping phase. An unavailable predecessor linear owner is not a
   successful transition. Nominal ProcessKey identity, actual Haskell maps,
   activation, selected partner, Close and disposal authority remain external. *)

Definition fsem02AdaptiveRemoveFreeOwner (site : nat) (owners : nat -> bool) : nat -> bool :=
  fun key => if Nat.eqb key site then false else owners key.

Definition fsem02AdaptiveResourceGatedPing
  (client server : nat) (owners : nat -> bool) before :=
  if owners client then
    if owners server then fsem02AdaptivePhaseJointPing client server before
    else None
  else None.

Theorem fsem02AdaptiveMissingFreeClientOwnerRefuses :
  forall client server owners before,
    fsem02AdaptiveResourceGatedPing client server
      (fsem02AdaptiveRemoveFreeOwner client owners) before = None.
Proof.
  intros client server owners before.
  unfold fsem02AdaptiveResourceGatedPing, fsem02AdaptiveRemoveFreeOwner.
  now rewrite Nat.eqb_refl.
Qed.

Theorem fsem02AdaptiveMissingFreeServerOwnerRefuses :
  forall client server owners before,
    client <> server ->
    fsem02AdaptiveResourceGatedPing client server
      (fsem02AdaptiveRemoveFreeOwner server owners) before = None.
Proof.
  intros client server owners before Hdiff.
  unfold fsem02AdaptiveResourceGatedPing, fsem02AdaptiveRemoveFreeOwner.
  assert (Hne : Nat.eqb client server = false).
  { apply Nat.eqb_neq; exact Hdiff. }
  rewrite Hne, Nat.eqb_refl.
  now destruct (owners client).
Qed.

Theorem fsem02AdaptiveRemoveFreeOwnerFramesSpectator :
  forall site spectator owners,
    site <> spectator ->
    fsem02AdaptiveRemoveFreeOwner site owners spectator = owners spectator.
Proof.
  intros site spectator owners Hdiff.
  unfold fsem02AdaptiveRemoveFreeOwner.
  assert (Hne : Nat.eqb spectator site = false).
  { apply Nat.eqb_neq. intro Heq. apply Hdiff. symmetry; exact Heq. }
  now rewrite Hne.
Qed.

Theorem fsem02AdaptiveMissingOwnerRefusalThenExplicitRetry :
  forall client server owners before successor,
    client <> server ->
    owners client = true ->
    owners server = true ->
    fsem02AdaptivePhaseJointPing client server before = Some successor ->
    fsem02AdaptiveResourceGatedPing client server
      (fsem02AdaptiveRemoveFreeOwner client owners) before = None /\
    fsem02AdaptiveResourceGatedPing client server
      (fsem02AdaptiveRemoveFreeOwner server owners) before = None /\
    fsem02AdaptiveResourceGatedPing client server owners before = Some successor.
Proof.
  intros client server owners before successor Hdiff Hclient Hserver Hphase.
  split.
  - apply fsem02AdaptiveMissingFreeClientOwnerRefuses.
  - split.
    + now apply fsem02AdaptiveMissingFreeServerOwnerRefuses.
    + unfold fsem02AdaptiveResourceGatedPing.
      now rewrite Hclient, Hserver.
Qed.
