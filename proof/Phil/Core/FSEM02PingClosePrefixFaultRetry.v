From Stdlib Require Import Arith.PeanoNat Logic.FunctionalExtensionality.
From Phil.Core Require Import Syntax Context FSEM02PingThreeProcessFrame
  FSEM02PingDisjointPairs FSEM02PingDisjointTerminalInterleavings.

(* Non-normative FSEM-02: a conditional finite-map *observation* of one
   local terminal Close attempt. 'admitted' is an external input standing for
   the native typed End/role/instance/outcome and ownership decision; it is
   NOT authorization inferred from a source spelling. The native process
   map, ProcessKey encoding, diagnostic priority and scheduler are not
   proved to refine this model. *)
Definition fsem02WriteOneProcess
  (process : nat) (closed : ResourceContext) (before : fsem02ProcessMap)
  : fsem02ProcessMap :=
  fun key => if Nat.eqb key process then Some closed else before key.

Inductive fsem02MapCloseAttempt : Type :=
  | FSEM02MapCloseRejected : fsem02ProcessMap -> fsem02MapCloseAttempt
  | FSEM02MapCloseApplied : fsem02ProcessMap -> fsem02MapCloseAttempt.

Definition fsem02TryMapClose
  (admitted : bool) (process : nat) (closed : ResourceContext)
  (before : fsem02ProcessMap) : fsem02MapCloseAttempt :=
  if admitted
  then FSEM02MapCloseApplied (fsem02WriteOneProcess process closed before)
  else FSEM02MapCloseRejected before.

Theorem fsem02MapCloseRefusalDoesNotModifyPrefix :
  forall process closed before,
    fsem02TryMapClose false process closed before =
      FSEM02MapCloseRejected before.
Proof. reflexivity. Qed.

Theorem fsem02MapCloseSuccessRecordsExactSite :
  forall process closed before,
    fsem02WriteOneProcess process closed before process = Some closed.
Proof.
  intros process closed before.
  unfold fsem02WriteOneProcess.
  now rewrite Nat.eqb_refl.
Qed.

Theorem fsem02MapCloseSuccessFramesOther :
  forall process other closed before,
    other <> process ->
    fsem02WriteOneProcess process closed before other = before other.
Proof.
  intros process other closed before Hdistinct.
  unfold fsem02WriteOneProcess.
  apply Nat.eqb_neq in Hdistinct.
  now rewrite Hdistinct.
Qed.

Theorem fsem02DisjointMapCloseWritesCommute :
  forall a b aClosed bClosed before,
    a <> b ->
    fsem02WriteOneProcess b bClosed
      (fsem02WriteOneProcess a aClosed before) =
    fsem02WriteOneProcess a aClosed
      (fsem02WriteOneProcess b bClosed before).
Proof.
  intros a b aClosed bClosed before Hdistinct.
  apply functional_extensionality; intro key.
  unfold fsem02WriteOneProcess.
  destruct (Nat.eqb key a) eqn:Ha;
  destruct (Nat.eqb key b) eqn:Hb;
  simpl; try reflexivity.
  apply Nat.eqb_eq in Ha.
  apply Nat.eqb_eq in Hb.
  congruence.
Qed.

Theorem fsem02MapCloseRefusalAfterIndependentCommitKeepsCommit :
  forall committed rejected committedClosed rejectedClosed before,
    fsem02TryMapClose false rejected rejectedClosed
      (fsem02WriteOneProcess committed committedClosed before) =
    FSEM02MapCloseRejected
      (fsem02WriteOneProcess committed committedClosed before).
Proof. reflexivity. Qed.

Theorem fsem02MapCloseValidRetryAfterRefusal :
  forall process closed before,
    match fsem02TryMapClose false process closed before with
    | FSEM02MapCloseRejected still =>
        fsem02TryMapClose true process closed still
    | FSEM02MapCloseApplied already => FSEM02MapCloseApplied already
    end =
    FSEM02MapCloseApplied (fsem02WriteOneProcess process closed before).
Proof. reflexivity. Qed.
