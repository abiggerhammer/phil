From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import Syntax Context FSEM02PingThreeProcessFrame
  FSEM02PingSharedClientContention FSEM02PingSharedServerTerminalCloseFrame.

(* Non-normative conditional process-map model. The source-derived End
   witnesses are checked in native Haskell; ResourceContext replacement and
   the one-use client token are explicitly modeled premises, not a native
   implementation refinement or source-derived authority grant. *)
Definition fsem02SharedClientProgressThenClose
  (client server : nat) (before : fsem02ProcessMap)
  (pair : option (ResourceContext * ResourceContext))
  (clientClosed serverClosed : ResourceContext)
  : option fsem02ProcessMap :=
  match fsem02SharedClientAttempt client server before true pair with
  | Some (progressed, false) =>
      Some (fsem02TerminalWriteOne server serverClosed
        (fsem02TerminalWriteOne client clientClosed progressed))
  | _ => None
  end.

Theorem fsem02SharedClientTerminalCloseOrdersAgree :
  forall client server (before : fsem02ProcessMap)
         clientClosed serverClosed key,
    client <> server ->
    fsem02TerminalWriteOne server serverClosed
      (fsem02TerminalWriteOne client clientClosed before) key =
    fsem02TerminalWriteOne client clientClosed
      (fsem02TerminalWriteOne server serverClosed before) key.
Proof. exact fsem02TerminalCloseOrdersAgreeAtEveryKey. Qed.

Theorem fsem02SharedClientTerminalCloseNoSuccessorWithoutPair :
  forall client server before clientClosed serverClosed,
    fsem02SharedClientProgressThenClose client server before
      None clientClosed serverClosed = None.
Proof. reflexivity. Qed.

Theorem fsem02SharedClientTerminalCloseExactClientSlot :
  forall client server before pair clientClosed serverClosed after,
    client <> server ->
    fsem02SharedClientProgressThenClose client server before
      pair clientClosed serverClosed = Some after ->
    after client = Some clientClosed.
Proof.
  intros client server before pair clientClosed serverClosed after
    Hdistinct H.
  unfold fsem02SharedClientProgressThenClose in H.
  destruct pair as [[clientAfter serverAfter]|]; simpl in H;
    try discriminate.
  inversion H; subst; clear H.
  unfold fsem02TerminalWriteOne.
  assert (Hother : Nat.eqb client server = false).
  { apply Nat.eqb_neq. exact Hdistinct. }
  rewrite Hother, Nat.eqb_refl. reflexivity.
Qed.

Theorem fsem02SharedClientTerminalCloseExactServerSlot :
  forall client server before pair clientClosed serverClosed after,
    fsem02SharedClientProgressThenClose client server before
      pair clientClosed serverClosed = Some after ->
    after server = Some serverClosed.
Proof.
  intros client server before pair clientClosed serverClosed after H.
  unfold fsem02SharedClientProgressThenClose in H.
  destruct pair as [[clientAfter serverAfter]|]; simpl in H;
    try discriminate.
  inversion H; subst; clear H.
  unfold fsem02TerminalWriteOne.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem fsem02SharedClientTerminalCloseFramesUnselectedServer :
  forall client selected unselected before pair clientClosed serverClosed after,
    unselected <> client ->
    unselected <> selected ->
    fsem02SharedClientProgressThenClose client selected before
      pair clientClosed serverClosed = Some after ->
    after unselected = before unselected.
Proof.
  intros client selected unselected before pair clientClosed serverClosed
    after HnotClient HnotServer H.
  unfold fsem02SharedClientProgressThenClose in H.
  destruct pair as [[clientAfter serverAfter]|]; simpl in H;
    try discriminate.
  inversion H; subst; clear H.
  unfold fsem02TerminalWriteOne, fsem02WriteTwoProcessContexts.
  assert (Hclient : Nat.eqb unselected client = false).
  { apply Nat.eqb_neq. exact HnotClient. }
  assert (Hserver : Nat.eqb unselected selected = false).
  { apply Nat.eqb_neq. exact HnotServer. }
  rewrite Hserver, Hclient. reflexivity.
Qed.

Theorem fsem02SharedClientTerminalCloseNeverRearmsClient :
  forall client server after candidate,
    fsem02SharedClientAttempt client server after false candidate = None.
Proof. reflexivity. Qed.
