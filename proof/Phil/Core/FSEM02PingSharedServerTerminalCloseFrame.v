From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import Syntax Context
  FSEM02PingThreeProcessFrame FSEM02PingSharedServerContention.

(* Non-normative bounded model.  A process key is a nat surrogate; a local
   Close is represented by an externally supplied ResourceContext replacement.
   The boolean in the shared-Server attempt remains an external one-use premise:
   neither source activation nor Haskell-to-Rocq fidelity follows from it. *)
Definition fsem02TerminalWriteOne
  (process : nat) (closed : ResourceContext) (before : fsem02ProcessMap)
  : fsem02ProcessMap :=
  fun key => if Nat.eqb key process then Some closed else before key.

Definition fsem02SharedServerProgressThenClose
  (client server : nat) (before : fsem02ProcessMap)
  (pair : option (ResourceContext * ResourceContext))
  (clientClosed serverClosed : ResourceContext)
  : option fsem02ProcessMap :=
  match fsem02SharedServerAttempt client server before true pair with
  | Some (progressed, false) =>
      Some (fsem02TerminalWriteOne server serverClosed
        (fsem02TerminalWriteOne client clientClosed progressed))
  | _ => None
  end.

Theorem fsem02TerminalCloseOrdersAgreeAtEveryKey :
  forall client server (before : fsem02ProcessMap)
         clientClosed serverClosed key,
    client <> server ->
    fsem02TerminalWriteOne server serverClosed
      (fsem02TerminalWriteOne client clientClosed before) key =
    fsem02TerminalWriteOne client clientClosed
      (fsem02TerminalWriteOne server serverClosed before) key.
Proof.
  intros client server before clientClosed serverClosed key Hdistinct.
  unfold fsem02TerminalWriteOne.
  destruct (Nat.eqb key client) eqn:Hclient;
    destruct (Nat.eqb key server) eqn:Hserver;
    try reflexivity.
  apply Nat.eqb_eq in Hclient.
  apply Nat.eqb_eq in Hserver.
  subst. contradiction.
Qed.

Theorem fsem02TerminalCloseNoSuccessorWithoutFirstStep :
  forall client server before clientClosed serverClosed,
    fsem02SharedServerProgressThenClose client server before
      None clientClosed serverClosed = None.
Proof. reflexivity. Qed.

Theorem fsem02TerminalCloseExactServerSlot :
  forall client server before pair clientClosed serverClosed after,
    fsem02SharedServerProgressThenClose client server before
      pair clientClosed serverClosed = Some after ->
    after server = Some serverClosed.
Proof.
  intros client server before pair clientClosed serverClosed after H.
  unfold fsem02SharedServerProgressThenClose in H.
  destruct pair as [[clientAfter serverAfter]|]; simpl in H;
    try discriminate.
  inversion H; subst; clear H.
  unfold fsem02TerminalWriteOne.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem fsem02TerminalCloseExactClientSlot :
  forall client server before pair clientClosed serverClosed after,
    client <> server ->
    fsem02SharedServerProgressThenClose client server before
      pair clientClosed serverClosed = Some after ->
    after client = Some clientClosed.
Proof.
  intros client server before pair clientClosed serverClosed after
    Hdistinct H.
  unfold fsem02SharedServerProgressThenClose in H.
  destruct pair as [[clientAfter serverAfter]|]; simpl in H;
    try discriminate.
  inversion H; subst; clear H.
  unfold fsem02TerminalWriteOne.
  assert (Hother : Nat.eqb client server = false).
  { apply Nat.eqb_neq. exact Hdistinct. }
  rewrite Hother, Nat.eqb_refl. reflexivity.
Qed.

Theorem fsem02TerminalCloseFramesUninvolvedProcess :
  forall client server spectator before pair clientClosed serverClosed after,
    spectator <> client ->
    spectator <> server ->
    fsem02SharedServerProgressThenClose client server before
      pair clientClosed serverClosed = Some after ->
    after spectator = before spectator.
Proof.
  intros client server spectator before pair clientClosed serverClosed
    after HnotClient HnotServer H.
  unfold fsem02SharedServerProgressThenClose in H.
  destruct pair as [[clientAfter serverAfter]|]; simpl in H;
    try discriminate.
  inversion H; subst; clear H.
  unfold fsem02TerminalWriteOne, fsem02WriteTwoProcessContexts.
  assert (Hclient : Nat.eqb spectator client = false).
  { apply Nat.eqb_neq. exact HnotClient. }
  assert (Hserver : Nat.eqb spectator server = false).
  { apply Nat.eqb_neq. exact HnotServer. }
  rewrite Hserver, Hclient.
  reflexivity.
Qed.

Theorem fsem02TerminalCloseNeverRearmsSpentServer :
  forall client server after candidate,
    fsem02SharedServerAttempt client server after false candidate = None.
Proof. reflexivity. Qed.
