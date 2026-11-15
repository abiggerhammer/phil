From Stdlib Require Import Arith.PeanoNat Logic.FunctionalExtensionality.

(* FSEM-02, non-normative *phase abstraction* for injected invalid Close
   attempts at every prefix of the three-Ping mixed-order regression.
   The per-process nat key and phase tagging are not certified Haskell
   ProcessKey or Session representations. External instance/role/ownership,
   activation, terminal authority, admitted scheduler and source checking
   are premises, NOT granted by this model. These three faults describe the
   deliberately chosen test requests, not a general error-priority theorem. *)
Inductive fsem02MixPhase : Type :=
| FSEM02AwaitPing | FSEM02LiveEnd | FSEM02Retired.

Inductive fsem02MixCloseFault : Type :=
| FSEM02PrematureHead | FSEM02WrongOutcome | FSEM02StaleEndpoint.

Definition fsem02MixPhaseMap : Type := nat -> fsem02MixPhase.

Definition fsem02MixWrite
  (site : nat) (value : fsem02MixPhase) (before : fsem02MixPhaseMap)
  : fsem02MixPhaseMap :=
  fun key => if Nat.eqb key site then value else before key.

Definition fsem02MixFaultFor (phase : fsem02MixPhase) : fsem02MixCloseFault :=
  match phase with
  | FSEM02AwaitPing => FSEM02PrematureHead
  | FSEM02LiveEnd => FSEM02WrongOutcome
  | FSEM02Retired => FSEM02StaleEndpoint
  end.

Definition fsem02MixBadClose
  (site : nat) (before : fsem02MixPhaseMap)
  : fsem02MixCloseFault * fsem02MixPhaseMap :=
  (fsem02MixFaultFor (before site), before).

Definition fsem02MixPing
  (site : nat) (before : fsem02MixPhaseMap)
  : option fsem02MixPhaseMap :=
  match before site with
  | FSEM02AwaitPing => Some (fsem02MixWrite site FSEM02LiveEnd before)
  | _ => None
  end.

Definition fsem02MixClose
  (site : nat) (before : fsem02MixPhaseMap)
  : option fsem02MixPhaseMap :=
  match before site with
  | FSEM02LiveEnd => Some (fsem02MixWrite site FSEM02Retired before)
  | _ => None
  end.

Theorem fsem02MixedPrefixPrematureFaultExact :
  forall site before, before site = FSEM02AwaitPing ->
    fst (fsem02MixBadClose site before) = FSEM02PrematureHead.
Proof. intros site before H; unfold fsem02MixBadClose; simpl; now rewrite H. Qed.

Theorem fsem02MixedPrefixWrongOutcomeFaultExact :
  forall site before, before site = FSEM02LiveEnd ->
    fst (fsem02MixBadClose site before) = FSEM02WrongOutcome.
Proof. intros site before H; unfold fsem02MixBadClose; simpl; now rewrite H. Qed.

Theorem fsem02MixedPrefixStaleFaultExact :
  forall site before, before site = FSEM02Retired ->
    fst (fsem02MixBadClose site before) = FSEM02StaleEndpoint.
Proof. intros site before H; unfold fsem02MixBadClose; simpl; now rewrite H. Qed.

Theorem fsem02MixedPrefixAllRefusalsPreserveEntireLedger :
  forall site before, snd (fsem02MixBadClose site before) = before.
Proof. reflexivity. Qed.

Theorem fsem02MixedPrefixIndependentSiteFrame :
  forall site spectator phase before,
    spectator <> site ->
    fsem02MixWrite site phase before spectator = before spectator.
Proof.
  intros site spectator phase before Hneq.
  unfold fsem02MixWrite.
  apply Nat.eqb_neq in Hneq.
  now rewrite Hneq.
Qed.

Theorem fsem02MixedPrefixValidCloseAfterRefusal :
  forall site before,
    before site = FSEM02LiveEnd ->
    fsem02MixClose site (snd (fsem02MixBadClose site before)) =
      Some (fsem02MixWrite site FSEM02Retired before).
Proof.
  intros site before H.
  unfold fsem02MixClose, fsem02MixBadClose; simpl.
  now rewrite H.
Qed.

Theorem fsem02MixedPrefixPingThenCloseAfterRefusal :
  forall site before,
    before site = FSEM02AwaitPing ->
    match fsem02MixPing site (snd (fsem02MixBadClose site before)) with
    | Some pinged => fsem02MixClose site pinged
    | None => None
    end = Some (fsem02MixWrite site FSEM02Retired before).
Proof.
  intros site before H.
  unfold fsem02MixBadClose; simpl.
  unfold fsem02MixPing; rewrite H.
  simpl.
  change (Some (fsem02MixWrite site FSEM02Retired
    (fsem02MixWrite site FSEM02LiveEnd before)) =
    Some (fsem02MixWrite site FSEM02Retired before)).
  f_equal.
  apply functional_extensionality; intro key.
  unfold fsem02MixWrite.
  destruct (Nat.eqb key site); reflexivity.
Qed.

Theorem fsem02MixedPrefixIndependentPhaseUpdatesCommute :
  forall a b phaseA phaseB before,
    a <> b ->
    fsem02MixWrite b phaseB (fsem02MixWrite a phaseA before) =
      fsem02MixWrite a phaseA (fsem02MixWrite b phaseB before).
Proof.
  intros a b phaseA phaseB before Hdistinct.
  apply functional_extensionality; intro key.
  unfold fsem02MixWrite.
  destruct (Nat.eqb key a) eqn:Ha;
  destruct (Nat.eqb key b) eqn:Hb; simpl; try reflexivity.
  apply Nat.eqb_eq in Ha.
  apply Nat.eqb_eq in Hb.
  congruence.
Qed.
