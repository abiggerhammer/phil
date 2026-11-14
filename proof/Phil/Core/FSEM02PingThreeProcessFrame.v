From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import Syntax Context FSEM02PingJointAtomicity.

(* Non-normative FSEM-02.  Process keys below are a finite representation
   surrogate, not a proof that native ProcessKey encodes as nat.  Activation,
   nominal protocol authority, map/loan fidelity, and source-to-model
   correspondence remain independently supplied premises. *)

Definition fsem02ProcessMap := nat -> option ResourceContext.

Definition fsem02WriteTwoProcessContexts
  (left right : nat) (leftAfter rightAfter : ResourceContext)
  (before : fsem02ProcessMap) : fsem02ProcessMap :=
  fun key =>
    if Nat.eqb key left then Some leftAfter
    else if Nat.eqb key right then Some rightAfter
    else before key.

Definition fsem02LiftTwoPartyResult
  (left right : nat) (before : fsem02ProcessMap)
  (pair : option (ResourceContext * ResourceContext))
  : option fsem02ProcessMap :=
  match pair with
  | None => None
  | Some (leftAfter, rightAfter) =>
      Some (fsem02WriteTwoProcessContexts left right leftAfter rightAfter before)
  end.

Theorem fsem02ThirdProcessRefusalHasNoSuccessor :
  forall left right before,
    fsem02LiftTwoPartyResult left right before None = None.
Proof. reflexivity. Qed.

Theorem fsem02ThirdProcessFrameOnPairSuccess :
  forall left right spectator before leftAfter rightAfter after,
    spectator <> left ->
    spectator <> right ->
    fsem02LiftTwoPartyResult left right before (Some (leftAfter, rightAfter))
      = Some after ->
    after spectator = before spectator.
Proof.
  intros left right spectator before leftAfter rightAfter after
    HotherLeft HotherRight Hsuccess.
  unfold fsem02LiftTwoPartyResult in Hsuccess.
  inversion Hsuccess; subst; clear Hsuccess.
  unfold fsem02WriteTwoProcessContexts.
  assert (Hleft : Nat.eqb spectator left = false).
  { apply Nat.eqb_neq. exact HotherLeft. }
  assert (Hright : Nat.eqb spectator right = false).
  { apply Nat.eqb_neq. exact HotherRight. }
  rewrite Hleft, Hright.
  reflexivity.
Qed.

Theorem fsem02ThreeProcessLeftSuccessorExact :
  forall left right before leftAfter rightAfter after,
    fsem02LiftTwoPartyResult left right before (Some (leftAfter, rightAfter))
      = Some after ->
    after left = Some leftAfter.
Proof.
  intros left right before leftAfter rightAfter after Hsuccess.
  unfold fsem02LiftTwoPartyResult in Hsuccess.
  inversion Hsuccess; subst; clear Hsuccess.
  unfold fsem02WriteTwoProcessContexts.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem fsem02ThreeProcessRightSuccessorExact :
  forall left right before leftAfter rightAfter after,
    left <> right ->
    fsem02LiftTwoPartyResult left right before (Some (leftAfter, rightAfter))
      = Some after ->
    after right = Some rightAfter.
Proof.
  intros left right before leftAfter rightAfter after Hdistinct Hsuccess.
  unfold fsem02LiftTwoPartyResult in Hsuccess.
  inversion Hsuccess; subst; clear Hsuccess.
  unfold fsem02WriteTwoProcessContexts.
  assert (HrightLeft : Nat.eqb right left = false).
  { apply Nat.eqb_neq. congruence. }
  rewrite HrightLeft, Nat.eqb_refl.
  reflexivity.
Qed.

(* Connect the frame to the existing separately proved conditional Ping pair.
   This is an external-input/finite-process-map lifting theorem, NOT proof of
   native Haskell Map mutation fidelity or source-generated process authority. *)
Definition fsem02ThreeProcessPing
  (left right : nat) (before : fsem02ProcessMap)
  (senderHead receiverHead : Session)
  (senderOld senderNext receiverOld receiverNext : Name)
  (senderBefore receiverBefore : ResourceContext)
  : option fsem02ProcessMap :=
  fsem02LiftTwoPartyResult left right before
    (fsem02PingJointResources senderHead receiverHead
      senderOld senderNext receiverOld receiverNext senderBefore receiverBefore).

Theorem fsem02ThreeProcessPingFramesUninvolved :
  forall left right spectator before senderHead receiverHead
         senderOld senderNext receiverOld receiverNext
         senderBefore receiverBefore after,
    spectator <> left ->
    spectator <> right ->
    fsem02ThreeProcessPing left right before senderHead receiverHead
      senderOld senderNext receiverOld receiverNext senderBefore receiverBefore
      = Some after ->
    after spectator = before spectator.
Proof.
  intros left right spectator before senderHead receiverHead
    senderOld senderNext receiverOld receiverNext senderBefore receiverBefore
    after Hleft Hright Hstep.
  unfold fsem02ThreeProcessPing in Hstep.
  destruct (fsem02PingJointResources senderHead receiverHead
    senderOld senderNext receiverOld receiverNext senderBefore receiverBefore)
    as [[leftAfter rightAfter]|] eqn:Hpair; simpl in Hstep;
    try discriminate.
  inversion Hstep; subst; clear Hstep.
  unfold fsem02WriteTwoProcessContexts.
  assert (HotherLeftEq : Nat.eqb spectator left = false).
  { apply Nat.eqb_neq. exact Hleft. }
  assert (HotherRightEq : Nat.eqb spectator right = false).
  { apply Nat.eqb_neq. exact Hright. }
  rewrite HotherLeftEq, HotherRightEq.
  reflexivity.
Qed.
