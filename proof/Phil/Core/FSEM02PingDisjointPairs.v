From Stdlib Require Import Arith.PeanoNat Logic.FunctionalExtensionality.
From Phil.Core Require Import Syntax Context FSEM02PingThreeProcessFrame.

(* FSEM-02 bounded non-normative interleaving model. All four process keys
   are assumed distinct, as are the externally admitted actual process
   contexts. No native ProcessKey representation theorem is asserted. *)

Definition fsem02TwoDisjointOrders
  (a b c d : nat) (before : fsem02ProcessMap)
  (first second : option (ResourceContext * ResourceContext))
  : option fsem02ProcessMap :=
  match fsem02LiftTwoPartyResult a b before first with
  | None => None
  | Some afterFirst =>
      fsem02LiftTwoPartyResult c d afterFirst second
  end.

Theorem fsem02TwoDisjointWritesCommute :
  forall a b c d acAfter asAfter bcAfter bsAfter before,
    a <> b -> a <> c -> a <> d ->
    b <> c -> b <> d -> c <> d ->
    fsem02WriteTwoProcessContexts c d bcAfter bsAfter
      (fsem02WriteTwoProcessContexts a b acAfter asAfter before) =
    fsem02WriteTwoProcessContexts a b acAfter asAfter
      (fsem02WriteTwoProcessContexts c d bcAfter bsAfter before).
Proof.
  intros a b c d acAfter asAfter bcAfter bsAfter before
    Hab Hac Had Hbc Hbd Hcd.
  apply functional_extensionality; intro key.
  unfold fsem02WriteTwoProcessContexts.
  destruct (Nat.eqb key a) eqn:Ha;
  destruct (Nat.eqb key b) eqn:Hb;
  destruct (Nat.eqb key c) eqn:Hc;
  destruct (Nat.eqb key d) eqn:Hd;
  simpl; try reflexivity;
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  end; congruence.
Qed.

Theorem fsem02TwoDisjointSuccessfulOrdersAgree :
  forall a b c d acAfter asAfter bcAfter bsAfter before,
    a <> b -> a <> c -> a <> d ->
    b <> c -> b <> d -> c <> d ->
    fsem02TwoDisjointOrders a b c d before
      (Some (acAfter, asAfter)) (Some (bcAfter, bsAfter)) =
    fsem02TwoDisjointOrders c d a b before
      (Some (bcAfter, bsAfter)) (Some (acAfter, asAfter)).
Proof.
  intros a b c d acAfter asAfter bcAfter bsAfter before
    Hab Hac Had Hbc Hbd Hcd.
  unfold fsem02TwoDisjointOrders, fsem02LiftTwoPartyResult; simpl.
  f_equal.
  apply fsem02TwoDisjointWritesCommute; assumption.
Qed.

Theorem fsem02FirstRefusedHasNoTwoPairSuccessor :
  forall a b c d before second,
    fsem02TwoDisjointOrders a b c d before None second = None.
Proof. reflexivity. Qed.

Theorem fsem02SecondRefusedHasNoTwoPairSuccessor :
  forall a b c d before first,
    fsem02TwoDisjointOrders a b c d before first None = None.
Proof.
  intros a b c d before [[leftAfter rightAfter]|]; reflexivity.
Qed.

Theorem fsem02TwoDisjointSuccessesFrameOther :
  forall a b c d acAfter asAfter bcAfter bsAfter before after spectator,
    spectator <> a -> spectator <> b ->
    spectator <> c -> spectator <> d ->
    fsem02TwoDisjointOrders a b c d before
      (Some (acAfter, asAfter)) (Some (bcAfter, bsAfter)) = Some after ->
    after spectator = before spectator.
Proof.
  intros a b c d acAfter asAfter bcAfter bsAfter before after spectator
    Hna Hnb Hnc Hnd Hsuccess.
  unfold fsem02TwoDisjointOrders, fsem02LiftTwoPartyResult in Hsuccess.
  simpl in Hsuccess.
  inversion Hsuccess; subst; clear Hsuccess.
  unfold fsem02WriteTwoProcessContexts.
  assert (Ha : Nat.eqb spectator a = false).
  { apply Nat.eqb_neq. exact Hna. }
  assert (Hb : Nat.eqb spectator b = false).
  { apply Nat.eqb_neq. exact Hnb. }
  assert (Hc : Nat.eqb spectator c = false).
  { apply Nat.eqb_neq. exact Hnc. }
  assert (Hd : Nat.eqb spectator d = false).
  { apply Nat.eqb_neq. exact Hnd. }
  rewrite Hc, Hd, Ha, Hb.
  reflexivity.
Qed.
