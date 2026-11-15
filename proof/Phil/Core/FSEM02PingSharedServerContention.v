From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import Syntax Context FSEM02PingThreeProcessFrame.

(* Non-normative mirror of overlapping-Client contention: the Server Receive
   predecessor belongs to one process key, with an externally supplied one-use
   availability flag. A flag is NOT a proof of native endpoint ownership. *)
Definition fsem02SharedServerAttempt
  (client server : nat) (before : fsem02ProcessMap)
  (unused : bool) (pair : option (ResourceContext * ResourceContext))
  : option (fsem02ProcessMap * bool) :=
  if unused then
    match pair with
    | Some (clientAfter, serverAfter) =>
        Some (fsem02WriteTwoProcessContexts client server
          clientAfter serverAfter before, false)
    | None => None
    end
  else None.

Definition fsem02SharedServerTwoAttempts
  (server clientA clientB : nat) (before : fsem02ProcessMap)
  (first second : option (ResourceContext * ResourceContext))
  : option fsem02ProcessMap :=
  match fsem02SharedServerAttempt clientA server before true first with
  | None => None
  | Some (afterFirst, unused) =>
      match fsem02SharedServerAttempt clientB server afterFirst unused second with
      | None => None
      | Some (afterSecond, _) => Some afterSecond
      end
  end.

Theorem fsem02SharedServerFirstConsumesToken :
  forall client server before clientAfter serverAfter after remaining,
    fsem02SharedServerAttempt client server before true
      (Some (clientAfter, serverAfter)) = Some (after, remaining) ->
    remaining = false.
Proof.
  intros client server before clientAfter serverAfter after remaining H.
  simpl in H. inversion H. reflexivity.
Qed.

Theorem fsem02SharedServerSecondRefusesAfterConsumption :
  forall client server before candidate,
    fsem02SharedServerAttempt client server before false candidate = None.
Proof. reflexivity. Qed.

Theorem fsem02SharedServerOverlapNeverHasTwoStepSuccessor :
  forall server clientA clientB before first second,
    fsem02SharedServerTwoAttempts server clientA clientB before
      first second = None.
Proof.
  intros server clientA clientB before
    [[clientAfter serverAfter]|] second; reflexivity.
Qed.

Theorem fsem02SharedServerFirstRefusalNoSuccessor :
  forall client server before,
    fsem02SharedServerAttempt client server before true None = None.
Proof. reflexivity. Qed.

Theorem fsem02SharedServerFirstSuccessorExact :
  forall client server before clientAfter serverAfter after,
    client <> server ->
    fsem02SharedServerAttempt client server before true
      (Some (clientAfter, serverAfter)) = Some (after, false) ->
    after server = Some serverAfter.
Proof.
  intros client server before clientAfter serverAfter after Hdistinct H.
  simpl in H. inversion H; subst; clear H.
  unfold fsem02WriteTwoProcessContexts.
  assert (Hs : Nat.eqb server client = false).
  { apply Nat.eqb_neq. congruence. }
  rewrite Hs, Nat.eqb_refl. reflexivity.
Qed.

Theorem fsem02SharedServerFirstClientSuccessorExact :
  forall client server before clientAfter serverAfter after,
    fsem02SharedServerAttempt client server before true
      (Some (clientAfter, serverAfter)) = Some (after, false) ->
    after client = Some clientAfter.
Proof.
  intros client server before clientAfter serverAfter after H.
  simpl in H. inversion H; subst; clear H.
  unfold fsem02WriteTwoProcessContexts.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem fsem02SharedServerFirstFramesUninvolved :
  forall client server spectator before clientAfter serverAfter after,
    spectator <> client -> spectator <> server ->
    fsem02SharedServerAttempt client server before true
      (Some (clientAfter, serverAfter)) = Some (after, false) ->
    after spectator = before spectator.
Proof.
  intros client server spectator before clientAfter serverAfter after
    HnotClient HnotServer H.
  simpl in H. inversion H; subst; clear H.
  unfold fsem02WriteTwoProcessContexts.
  assert (Hc : Nat.eqb spectator client = false).
  { apply Nat.eqb_neq. exact HnotClient. }
  assert (Hs : Nat.eqb spectator server = false).
  { apply Nat.eqb_neq. exact HnotServer. }
  rewrite Hc, Hs. reflexivity.
Qed.
