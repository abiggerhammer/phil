From Stdlib Require Import Arith.PeanoNat Logic.FunctionalExtensionality.
From Phil.Core Require Import Syntax Context FSEM02PingThreeProcessFrame
  FSEM02PingClosePrefixFaultRetry FSEM02PingTripleDisjointTerminal.

(* Non-normative FSEM-02. Nat process keys are representation surrogates.
   Each Ping or terminal Close update is independently admitted externally:
   no source-derived activation, nominal authority or disposal permission. *)

Theorem fsem02MixedIndependentCloseCommutesWithPair :
  forall a b c aClosed bNext cNext before,
    a <> b -> a <> c ->
    fsem02WriteOneProcess a aClosed
      (fsem02WriteTwoProcessContexts b c bNext cNext before) =
    fsem02WriteTwoProcessContexts b c bNext cNext
      (fsem02WriteOneProcess a aClosed before).
Proof.
  intros a b c aClosed bNext cNext before Hab Hac.
  apply functional_extensionality; intro key.
  unfold fsem02WriteOneProcess, fsem02WriteTwoProcessContexts.
  destruct (Nat.eqb key a) eqn:Ha;
  destruct (Nat.eqb key b) eqn:Hb;
  destruct (Nat.eqb key c) eqn:Hc;
  simpl; try reflexivity;
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  end; congruence.
Qed.

Theorem fsem02MixedTwoClosesCommutePastOtherPair :
  forall a d b c aClosed dClosed bNext cNext before,
    a <> b -> a <> c -> d <> b -> d <> c ->
    fsem02WriteOneProcess d dClosed
      (fsem02WriteOneProcess a aClosed
        (fsem02WriteTwoProcessContexts b c bNext cNext before)) =
    fsem02WriteTwoProcessContexts b c bNext cNext
      (fsem02WriteOneProcess d dClosed
        (fsem02WriteOneProcess a aClosed before)).
Proof.
  intros a d b c aClosed dClosed bNext cNext before
    Hab Hac Hdb Hdc.
  rewrite (fsem02MixedIndependentCloseCommutesWithPair
    a b c aClosed bNext cNext before Hab Hac).
  rewrite (fsem02MixedIndependentCloseCommutesWithPair
    d b c dClosed bNext cNext _ Hdb Hdc).
  reflexivity.
Qed.

Theorem fsem02MixedIndependentPairCannotEraseClosedSite :
  forall a b c aClosed bNext cNext before,
    a <> b -> a <> c ->
    fsem02WriteTwoProcessContexts b c bNext cNext
      (fsem02WriteOneProcess a aClosed before) a = Some aClosed.
Proof.
  intros a b c aClosed bNext cNext before Hab Hac.
  unfold fsem02WriteTwoProcessContexts.
  assert (Hb : Nat.eqb a b = false).
  { apply Nat.eqb_neq; exact Hab. }
  assert (Hc : Nat.eqb a c = false).
  { apply Nat.eqb_neq; exact Hac. }
  rewrite Hb, Hc.
  apply fsem02MapCloseSuccessRecordsExactSite.
Qed.

Theorem fsem02MixedCloseAndPairFrameSpectator :
  forall a b c spectator aClosed bNext cNext before,
    spectator <> a -> spectator <> b -> spectator <> c ->
    fsem02WriteOneProcess a aClosed
      (fsem02WriteTwoProcessContexts b c bNext cNext before) spectator =
    before spectator.
Proof.
  intros a b c spectator aClosed bNext cNext before Ha Hb Hc.
  rewrite (fsem02MapCloseSuccessFramesOther a spectator aClosed _ Ha).
  unfold fsem02WriteTwoProcessContexts.
  assert (Hbeq : Nat.eqb spectator b = false).
  { apply Nat.eqb_neq; exact Hb. }
  assert (Hceq : Nat.eqb spectator c = false).
  { apply Nat.eqb_neq; exact Hc. }
  now rewrite Hbeq, Hceq.
Qed.

Theorem fsem02MixedRefusedPrematureCloseKeepsPairState :
  forall b c rejected rejectedClosed bNext cNext before,
    fsem02TryMapClose false rejected rejectedClosed
      (fsem02WriteTwoProcessContexts b c bNext cNext before) =
    FSEM02MapCloseRejected
      (fsem02WriteTwoProcessContexts b c bNext cNext before).
Proof. reflexivity. Qed.

Theorem fsem02MixedRetryAfterIndependentPairRefusal :
  forall a b c aClosed bNext cNext before,
    match fsem02TryMapClose false a aClosed
      (fsem02WriteTwoProcessContexts b c bNext cNext before) with
    | FSEM02MapCloseRejected prefix =>
        fsem02TryMapClose true a aClosed prefix
    | FSEM02MapCloseApplied already =>
        FSEM02MapCloseApplied already
    end =
      FSEM02MapCloseApplied
        (fsem02WriteOneProcess a aClosed
          (fsem02WriteTwoProcessContexts b c bNext cNext before)).
Proof. reflexivity. Qed.
