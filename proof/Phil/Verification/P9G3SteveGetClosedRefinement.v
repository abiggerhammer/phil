From Coq Require Import Arith.PeanoNat Lia.

(*
  P9-G3, R1b/R2: isolated *candidate* closed-fragment semantics for the
  selected SteveGet control shape. No interpretation of Phil's actual
  Surface evaluator, actual manually authored Core execution, Haskell
  implementation, LLVM, selected native binary, or provider law is
  postulated here. The missing source/Core adequacy/refinement obligations
  are explicit in the companion review document. These are pure model facts.

  In particular the source/Core world here carries mathematical owner
  incarnations, not Haskell StablePtr bits, source binder spelling, SHA-256
  content equality, or a runtime credential.
*)

Record P9Pin : Type := P9MkPin {
  p9_run : nat;
  p9_content_id : nat;
  p9_instance_k : nat;
  p9_instance_i : nat
}.

Record P9Owner : Type := P9MkOwner {
  p9_owner_run : nat;
  p9_owner_serial : nat
}.

Record P9Loan : Type := P9MkLoan {
  p9_loan_owner : P9Owner;
  p9_loan_serial : nat
}.

Inductive P9Digest : Type := P9Accept | P9Reject.
Inductive P9Exit : Type :=
  | P9Success | P9IntegrityFailure | P9NotFound | P9StorageFailure.

Definition p9_digest_exit (d : P9Digest) : P9Exit :=
  match d with
  | P9Accept => P9Success
  | P9Reject => P9IntegrityFailure
  end.

(*
  Source loan-open/close are separate from the digest operation and the
  owner release; in the real get.phil the loan closes *before* deciding
  between the accepted/rejected release branches.
*)
Inductive P9SourceState : Type :=
  | P9SEntry (p : P9Pin)
  | P9SAwait (p : P9Pin)
  | P9SFound (p : P9Pin) (o : P9Owner)
  | P9SBorrow (p : P9Pin) (o : P9Owner) (l : P9Loan)
  | P9SChecked (p : P9Pin) (o : P9Owner) (l : P9Loan) (d : P9Digest)
  | P9SClosed (p : P9Pin) (o : P9Owner) (d : P9Digest)
  | P9SReleased (p : P9Pin) (d : P9Digest)
  | P9SNoOwner (p : P9Pin) (x : P9Exit)
  | P9SDone (p : P9Pin) (x : P9Exit).

Inductive p9_source_step : P9SourceState -> P9SourceState -> Prop :=
  | P9SrcCall : forall p,
      p9_source_step (P9SEntry p) (P9SAwait p)
  | P9SrcFound : forall p serial,
      p9_source_step (P9SAwait p)
        (P9SFound p (P9MkOwner (p9_run p) serial))
  | P9SrcMissing : forall p,
      p9_source_step (P9SAwait p) (P9SNoOwner p P9NotFound)
  | P9SrcStorage : forall p,
      p9_source_step (P9SAwait p) (P9SNoOwner p P9StorageFailure)
  | P9SrcOpen : forall p o serial,
      p9_source_step (P9SFound p o)
        (P9SBorrow p o (P9MkLoan o serial))
  | P9SrcDigest : forall p o l result,
      p9_source_step (P9SBorrow p o l)
        (P9SChecked p o l result)
  | P9SrcClose : forall p o l result,
      p9_source_step (P9SChecked p o l result)
        (P9SClosed p o result)
  | P9SrcRelease : forall p o result,
      p9_source_step (P9SClosed p o result)
        (P9SReleased p result)
  | P9SrcReturnFound : forall p result,
      p9_source_step (P9SReleased p result)
        (P9SDone p (p9_digest_exit result))
  | P9SrcReturnOther : forall p x,
      p9_source_step (P9SNoOwner p x) (P9SDone p x).

(* Owner is tied to this invocation; the loan's owner is not a pointer. *)
Definition p9_source_well_scoped (s : P9SourceState) : Prop :=
  match s with
  | P9SFound p o =>
      p9_owner_run o = p9_run p
  | P9SBorrow p o l =>
      p9_owner_run o = p9_run p /\ p9_loan_owner l = o
  | P9SChecked p o l _ =>
      p9_owner_run o = p9_run p /\ p9_loan_owner l = o
  | P9SClosed p o _ =>
      p9_owner_run o = p9_run p
  | _ => True
  end.

Lemma p9_source_step_preserves_scope :
  forall s s', p9_source_step s s' ->
    p9_source_well_scoped s -> p9_source_well_scoped s'.
Proof.
  intros s s' Step Valid.
  destruct Step; simpl in *; intuition auto.
Qed.

Inductive p9_source_reachable (entry : P9Pin) : P9SourceState -> Prop :=
  | P9ReachEntry : p9_source_reachable entry (P9SEntry entry)
  | P9ReachNext : forall a b, p9_source_reachable entry a ->
      p9_source_step a b -> p9_source_reachable entry b.

Theorem p9_r1b_model_reachable_scoped :
  forall entry s, p9_source_reachable entry s ->
    p9_source_well_scoped s.
Proof.
  intros entry s Reach.
  induction Reach.
  - simpl. exact I.
  - eapply p9_source_step_preserves_scope; eauto.
Qed.

Theorem p9_r1b_model_digest_live_original_loan :
  forall entry s p owner loan result,
    p9_source_reachable entry s ->
    p9_source_step s (P9SChecked p owner loan result) ->
    s = P9SBorrow p owner loan /\
    p9_owner_run owner = p9_run p /\
    p9_loan_owner loan = owner.
Proof.
  intros entry s p owner loan result Reach Step.
  inversion Step; subst.
  split; [reflexivity |].
  eapply p9_r1b_model_reachable_scoped in Reach.
  exact Reach.
Qed.

Definition p9_source_rank (s : P9SourceState) : nat :=
  match s with
  | P9SEntry _ => 8
  | P9SAwait _ => 7
  | P9SFound _ _ => 6
  | P9SBorrow _ _ _ => 5
  | P9SChecked _ _ _ _ => 4
  | P9SClosed _ _ _ => 3
  | P9SReleased _ _ => 2
  | P9SNoOwner _ _ => 2
  | P9SDone _ _ => 0
  end.

Theorem p9_r1b_model_strict_step_rank :
  forall a b, p9_source_step a b ->
    p9_source_rank b < p9_source_rank a.
Proof.
  intros a b Step. destruct Step; simpl; lia.
Qed.

(* The selected Core projection has no explicit loan open/close events. *)
Inductive P9CoreState : Type :=
  | P9CEntry (p : P9Pin)
  | P9CAwait (p : P9Pin)
  | P9CFound (p : P9Pin) (o : P9Owner)
  | P9CChecked (p : P9Pin) (o : P9Owner) (d : P9Digest)
  | P9CReleased (p : P9Pin) (d : P9Digest)
  | P9CNoOwner (p : P9Pin) (x : P9Exit)
  | P9CDone (p : P9Pin) (x : P9Exit).

Inductive p9_core_step : P9CoreState -> P9CoreState -> Prop :=
  | P9CoreCall : forall p,
      p9_core_step (P9CEntry p) (P9CAwait p)
  | P9CoreFound : forall p serial,
      p9_core_step (P9CAwait p)
        (P9CFound p (P9MkOwner (p9_run p) serial))
  | P9CoreMissing : forall p,
      p9_core_step (P9CAwait p) (P9CNoOwner p P9NotFound)
  | P9CoreStorage : forall p,
      p9_core_step (P9CAwait p) (P9CNoOwner p P9StorageFailure)
  | P9CoreDigest : forall p o result,
      p9_core_step (P9CFound p o) (P9CChecked p o result)
  | P9CoreRelease : forall p o result,
      p9_core_step (P9CChecked p o result) (P9CReleased p result)
  | P9CoreReturnFound : forall p result,
      p9_core_step (P9CReleased p result)
        (P9CDone p (p9_digest_exit result))
  | P9CoreReturnOther : forall p x,
      p9_core_step (P9CNoOwner p x) (P9CDone p x).

Definition p9_erase_source (s : P9SourceState) : P9CoreState :=
  match s with
  | P9SEntry p => P9CEntry p
  | P9SAwait p => P9CAwait p
  | P9SFound p o => P9CFound p o
  | P9SBorrow p o _ => P9CFound p o
  | P9SChecked p o _ d => P9CChecked p o d
  | P9SClosed p o d => P9CChecked p o d
  | P9SReleased p d => P9CReleased p d
  | P9SNoOwner p x => P9CNoOwner p x
  | P9SDone p x => P9CDone p x
  end.

(*
  R2: every *modeled* original-source transition either stutters at the
  selected Core boundary (loan open/close), or maps to one Core step.
  This is NOT a general compiler theorem and is not yet a proof that
  the actual, manually authored SteveGet Core obeys this semantics.
*)
Theorem p9_r2_model_source_to_core_weak_step :
  forall s s', p9_source_step s s' ->
    p9_erase_source s = p9_erase_source s' \/
    p9_core_step (p9_erase_source s) (p9_erase_source s').
Proof.
  intros s s' Step.
  destruct Step; simpl; try (left; reflexivity);
    right; constructor.
Qed.

Definition p9_core_well_scoped (s : P9CoreState) : Prop :=
  match s with
  | P9CFound p o => p9_owner_run o = p9_run p
  | P9CChecked p o _ => p9_owner_run o = p9_run p
  | _ => True
  end.

Lemma p9_core_step_preserves_scope :
  forall c c', p9_core_step c c' ->
    p9_core_well_scoped c -> p9_core_well_scoped c'.
Proof.
  intros c c' Step Good.
  destruct Step; simpl in *; auto.
Qed.

Inductive p9_core_reachable (entry : P9Pin) : P9CoreState -> Prop :=
  | P9CoreReachEntry : p9_core_reachable entry (P9CEntry entry)
  | P9CoreReachNext : forall a b, p9_core_reachable entry a ->
      p9_core_step a b -> p9_core_reachable entry b.

Theorem p9_r2_model_core_reachable_scoped :
  forall entry c, p9_core_reachable entry c ->
    p9_core_well_scoped c.
Proof.
  intros entry c Reach.
  induction Reach.
  - simpl. exact I.
  - eapply p9_core_step_preserves_scope; eauto.
Qed.

(* Safety on ALL modeled target digest transitions, not mere forward
   simulation existence. A target input with a different run identity
   cannot be related to the same original invocation's found owner. *)
Theorem p9_r2_model_target_digest_original_invocation :
  forall entry c p owner result,
    p9_core_reachable entry c ->
    p9_core_step c (P9CChecked p owner result) ->
    c = P9CFound p owner /\
    p9_owner_run owner = p9_run p.
Proof.
  intros entry c p owner result Reach Step.
  inversion Step; subst.
  split; [reflexivity |].
  eapply p9_r2_model_core_reachable_scoped in Reach.
  exact Reach.
Qed.

Theorem p9_r2_model_distinct_owners_even_equal_bytes :
  forall runA runB serialA serialB,
    runA <> runB ->
    P9MkOwner runA serialA <> P9MkOwner runB serialB.
Proof.
  intros runA runB serialA serialB Distinct Equal.
  inversion Equal. contradiction.
Qed.

Print Assumptions p9_r1b_model_reachable_scoped.
Print Assumptions p9_r1b_model_digest_live_original_loan.
Print Assumptions p9_r1b_model_strict_step_rank.
Print Assumptions p9_r2_model_source_to_core_weak_step.
Print Assumptions p9_r2_model_core_reachable_scoped.
Print Assumptions p9_r2_model_target_digest_original_invocation.
Print Assumptions p9_r2_model_distinct_owners_even_equal_bytes.
