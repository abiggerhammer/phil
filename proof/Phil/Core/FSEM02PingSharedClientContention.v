From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import Syntax Context FSEM02PingThreeProcessFrame.

(* Non-normative representation: common Client key and externally supplied
   predecessor availability. No native ProcessKey/token representation theorem. *)
Definition fsem02SharedClientAttempt
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

Definition fsem02SharedClientTwoAttempts
  (client serverA serverB : nat) (before : fsem02ProcessMap)
  (first second : option (ResourceContext * ResourceContext))
  : option fsem02ProcessMap :=
  match fsem02SharedClientAttempt client serverA before true first with
  | None => None
  | Some (afterFirst, unused) =>
      match fsem02SharedClientAttempt client serverB afterFirst unused second with
      | None => None
      | Some (afterSecond, _) => Some afterSecond
      end
  end.

Theorem fsem02SharedClientFirstConsumesToken :
  forall client server before clientAfter serverAfter after remaining,
    fsem02SharedClientAttempt client server before true
      (Some (clientAfter, serverAfter)) = Some (after, remaining) ->
    remaining = false.
Proof.
  intros client server before clientAfter serverAfter after remaining H.
  simpl in H. inversion H. reflexivity.
Qed.

Theorem fsem02SharedClientSecondRefusesAfterConsumption :
  forall client server before candidate,
    fsem02SharedClientAttempt client server before false candidate = None.
Proof. reflexivity. Qed.

Theorem fsem02SharedClientOverlapNeverHasTwoStepSuccessor :
  forall client serverA serverB before first second,
    fsem02SharedClientTwoAttempts client serverA serverB before
      first second = None.
Proof.
  intros client serverA serverB before
    [[clientAfter serverAfter]|] second; reflexivity.
Qed.

Theorem fsem02SharedClientFirstRefusalNoSuccessor :
  forall client server before,
    fsem02SharedClientAttempt client server before true None = None.
Proof. reflexivity. Qed.

Theorem fsem02SharedClientFirstSuccessorExact :
  forall client server before clientAfter serverAfter after,
    fsem02SharedClientAttempt client server before true
      (Some (clientAfter, serverAfter)) = Some (after, false) ->
    after client = Some clientAfter.
Proof.
  intros client server before clientAfter serverAfter after H.
  simpl in H. inversion H; subst; clear H.
  unfold fsem02WriteTwoProcessContexts.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem fsem02SharedClientFirstFramesUninvolved :
  forall client server spectator before clientAfter serverAfter after,
    spectator <> client -> spectator <> server ->
    fsem02SharedClientAttempt client server before true
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
