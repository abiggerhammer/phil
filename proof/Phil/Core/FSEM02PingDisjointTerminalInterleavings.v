From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import Syntax Context FSEM02PingThreeProcessFrame
  FSEM02PingDisjointPairs.

(* Conditional finite nat-key process map. Pair success, exact closed
   ResourceContexts, and nominal activation/disposal are external premises.
   This is not a proof of native Close or ProcessKey representation fidelity. *)
Definition fsem02DisjointPingTerminal
  (a b c d : nat) (before : fsem02ProcessMap)
  (first second : option (ResourceContext * ResourceContext))
  (aClosed bClosed cClosed dClosed : ResourceContext)
  : option fsem02ProcessMap :=
  match fsem02TwoDisjointOrders a b c d before first second with
  | None => None
  | Some progressed =>
      Some (fsem02WriteTwoProcessContexts c d cClosed dClosed
        (fsem02WriteTwoProcessContexts a b aClosed bClosed progressed))
  end.

Theorem fsem02DisjointTerminalFirstRefusalNoSuccessor :
  forall a b c d before second ac bc cc dc,
    fsem02DisjointPingTerminal a b c d before None second
      ac bc cc dc = None.
Proof. reflexivity. Qed.

Theorem fsem02DisjointTerminalSecondRefusalNoSuccessor :
  forall a b c d before first ac bc cc dc,
    fsem02DisjointPingTerminal a b c d before first None
      ac bc cc dc = None.
Proof.
  intros a b c d before [[pa pb]|] ac bc cc dc; reflexivity.
Qed.

Theorem fsem02DisjointTerminalPairScheduleCommutation :
  forall a b c d pa pb pc pd ac bc cc dc before,
    a <> b -> a <> c -> a <> d ->
    b <> c -> b <> d -> c <> d ->
    fsem02DisjointPingTerminal a b c d before
      (Some (pa, pb)) (Some (pc, pd)) ac bc cc dc =
    fsem02DisjointPingTerminal c d a b before
      (Some (pc, pd)) (Some (pa, pb)) cc dc ac bc.
Proof.
  intros a b c d pa pb pc pd ac bc cc dc before
    Hab Hac Had Hbc Hbd Hcd.
  unfold fsem02DisjointPingTerminal.
  rewrite (fsem02TwoDisjointSuccessfulOrdersAgree
    a b c d pa pb pc pd before Hab Hac Had Hbc Hbd Hcd).
  simpl.
  f_equal.
  apply fsem02TwoDisjointWritesCommute; assumption.
Qed.

Theorem fsem02DisjointTerminalExactFirstClient :
  forall a b c d before pa pb pc pd ac bc cc dc after,
    a <> c -> a <> d ->
    fsem02DisjointPingTerminal a b c d before
      (Some (pa, pb)) (Some (pc, pd)) ac bc cc dc = Some after ->
    after a = Some ac.
Proof.
  intros a b c d before pa pb pc pd ac bc cc dc after Hac Had H.
  unfold fsem02DisjointPingTerminal, fsem02TwoDisjointOrders,
    fsem02LiftTwoPartyResult in H.
  simpl in H. inversion H; subst; clear H.
  unfold fsem02WriteTwoProcessContexts.
  assert (Hc : Nat.eqb a c = false).
  { apply Nat.eqb_neq. exact Hac. }
  assert (Hd : Nat.eqb a d = false).
  { apply Nat.eqb_neq. exact Had. }
  rewrite Hc, Hd, Nat.eqb_refl. reflexivity.
Qed.

Theorem fsem02DisjointTerminalExactSecondServer :
  forall a b c d before pa pb pc pd ac bc cc dc after,
    c <> d ->
    fsem02DisjointPingTerminal a b c d before
      (Some (pa, pb)) (Some (pc, pd)) ac bc cc dc = Some after ->
    after d = Some dc.
Proof.
  intros a b c d before pa pb pc pd ac bc cc dc after Hcd H.
  unfold fsem02DisjointPingTerminal, fsem02TwoDisjointOrders,
    fsem02LiftTwoPartyResult in H.
  simpl in H. inversion H; subst; clear H.
  unfold fsem02WriteTwoProcessContexts.
  assert (Hc : Nat.eqb d c = false).
  { apply Nat.eqb_neq. congruence. }
  rewrite Hc, Nat.eqb_refl. reflexivity.
Qed.

Theorem fsem02DisjointTerminalFramesOther :
  forall a b c d before pa pb pc pd ac bc cc dc after spectator,
    spectator <> a -> spectator <> b ->
    spectator <> c -> spectator <> d ->
    fsem02DisjointPingTerminal a b c d before
      (Some (pa, pb)) (Some (pc, pd)) ac bc cc dc = Some after ->
    after spectator = before spectator.
Proof.
  intros a b c d before pa pb pc pd ac bc cc dc after spectator
    Ha Hb Hc Hd H.
  unfold fsem02DisjointPingTerminal, fsem02TwoDisjointOrders,
    fsem02LiftTwoPartyResult in H.
  simpl in H. inversion H; subst; clear H.
  unfold fsem02WriteTwoProcessContexts.
  assert (Ea : Nat.eqb spectator a = false).
  { apply Nat.eqb_neq. exact Ha. }
  assert (Eb : Nat.eqb spectator b = false).
  { apply Nat.eqb_neq. exact Hb. }
  assert (Ec : Nat.eqb spectator c = false).
  { apply Nat.eqb_neq. exact Hc. }
  assert (Ed : Nat.eqb spectator d = false).
  { apply Nat.eqb_neq. exact Hd. }
  rewrite Ea, Eb, Ec, Ed. reflexivity.
Qed.
