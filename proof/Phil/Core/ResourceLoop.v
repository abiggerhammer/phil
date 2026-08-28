From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List.
Import ListNotations.

From Phil.Core Require Import ResourceJoin.

(*
  PHIL-RES-LOOP-001 — loop state telescope re-entry and explicit
  propositional transport.

  PHIL-RES-JOIN-001 already certifies the generalized state-projection
  relation used by ordinary joins.  This theorem deliberately reuses that
  exact relation for loop initial entry and every continue/backedge rather than
  introducing a second ownership/subject rule for loops.

  RES-009 contributes the exact LoopContract telescope discipline: every
  accepted loop predecessor uses the same declared slot domain and slot
  requirements, and each projection separately satisfies ResourceProjectionSuccess.

  RES-010 contributes the propositional-transport discipline: definitional
  equality needs no extra witness, but a non-definitional index change is
  admitted only through explicit accepted equality evidence.  The concrete
  Core VTransport checker and source-to-Systems correspondence remain a later
  implementation/correspondence boundary.

  RES-013 logical invariant establishment is intentionally NOT discharged here.
  Structural loop-state compatibility does not establish an arbitrary logical
  invariant; PHIL-RES-INVARIANT-001 owns that separate claim.
*)

Record LoopStateTelescope : Type := mkLoopStateTelescope {
  loopStateSlots : ResourceSlot -> bool;
  loopStateRequirements : ResourceSlot -> ResourceSlotRequirement
}.

Definition ProjectionUsesLoopTelescope
  (telescope : LoopStateTelescope)
  (projection : ResourceProjection) : Prop :=
  (forall slot,
    loopStateSlots telescope slot = true <->
      exists owner, projectionBindings projection slot = Some owner) /\
  (forall slot,
    loopStateSlots telescope slot = true ->
    projectionRequirements projection slot = loopStateRequirements telescope slot).

Inductive LoopProjectionKind : Type :=
| LoopInitialEntry
| LoopBackedge.

Record LoopStateProjection : Type := mkLoopStateProjection {
  loopProjectionKind : LoopProjectionKind;
  loopProjectionResource : ResourceProjection
}.

Definition LoopProjectionAccepted
  (succession : SuccessionEvidence)
  (telescope : LoopStateTelescope)
  (projection : LoopStateProjection) : Prop :=
  ResourceProjectionSuccess succession (loopProjectionResource projection) /\
  ProjectionUsesLoopTelescope telescope (loopProjectionResource projection).

Definition LoopInitialAccepted
  (succession : SuccessionEvidence)
  (telescope : LoopStateTelescope)
  (projection : LoopStateProjection) : Prop :=
  loopProjectionKind projection = LoopInitialEntry /\
  LoopProjectionAccepted succession telescope projection.

Definition LoopBackedgeAccepted
  (succession : SuccessionEvidence)
  (telescope : LoopStateTelescope)
  (projection : LoopStateProjection) : Prop :=
  loopProjectionKind projection = LoopBackedge /\
  LoopProjectionAccepted succession telescope projection.

Theorem accepted_loop_projection_uses_join_projection_relation :
  forall succession telescope projection,
    LoopProjectionAccepted succession telescope projection ->
    ResourceProjectionSuccess succession (loopProjectionResource projection).
Proof.
  intros succession telescope projection Haccepted.
  exact (proj1 Haccepted).
Qed.

Theorem accepted_loop_projection_uses_declared_telescope :
  forall succession telescope projection,
    LoopProjectionAccepted succession telescope projection ->
    ProjectionUsesLoopTelescope telescope (loopProjectionResource projection).
Proof.
  intros succession telescope projection Haccepted.
  exact (proj2 Haccepted).
Qed.

Theorem loop_initial_and_backedge_share_declared_telescope :
  forall succession telescope initial backedge,
    LoopInitialAccepted succession telescope initial ->
    LoopBackedgeAccepted succession telescope backedge ->
    ProjectionUsesLoopTelescope telescope (loopProjectionResource initial) /\
    ProjectionUsesLoopTelescope telescope (loopProjectionResource backedge).
Proof.
  intros succession telescope initial backedge Hinitial Hbackedge.
  unfold LoopInitialAccepted in Hinitial.
  unfold LoopBackedgeAccepted in Hbackedge.
  destruct Hinitial as [_ HinitialAccepted].
  destruct Hbackedge as [_ HbackedgeAccepted].
  split.
  - eapply accepted_loop_projection_uses_declared_telescope.
    exact HinitialAccepted.
  - eapply accepted_loop_projection_uses_declared_telescope.
    exact HbackedgeAccepted.
Qed.

Theorem declared_loop_slot_is_present_on_every_accepted_projection :
  forall succession telescope projection slot,
    LoopProjectionAccepted succession telescope projection ->
    loopStateSlots telescope slot = true ->
    exists owner,
      projectionBindings (loopProjectionResource projection) slot = Some owner.
Proof.
  intros succession telescope projection slot Haccepted Hdeclared.
  destruct Haccepted as [_ [Hslots _]].
  apply (proj1 (Hslots slot)).
  exact Hdeclared.
Qed.

Theorem undeclared_loop_slot_cannot_be_synthesized :
  forall succession telescope projection slot owner,
    LoopProjectionAccepted succession telescope projection ->
    loopStateSlots telescope slot = false ->
    projectionBindings (loopProjectionResource projection) slot <> Some owner.
Proof.
  intros succession telescope projection slot owner Haccepted Habsent Hbound.
  destruct Haccepted as [_ [Hslots _]].
  pose proof (proj2 (Hslots slot)) as HboundImpliesDeclared.
  specialize (HboundImpliesDeclared (ex_intro _ owner Hbound)).
  rewrite Habsent in HboundImpliesDeclared.
  discriminate.
Qed.

Theorem accepted_loop_projection_uses_exact_slot_requirement :
  forall succession telescope projection slot,
    LoopProjectionAccepted succession telescope projection ->
    loopStateSlots telescope slot = true ->
    projectionRequirements (loopProjectionResource projection) slot =
      loopStateRequirements telescope slot.
Proof.
  intros succession telescope projection slot Haccepted Hdeclared.
  destruct Haccepted as [_ [_ Hrequirements]].
  apply Hrequirements.
  exact Hdeclared.
Qed.

Theorem accepted_loop_fixed_slot_is_subject_justified :
  forall succession telescope projection slot owner expected,
    LoopProjectionAccepted succession telescope projection ->
    loopStateSlots telescope slot = true ->
    projectionBindings (loopProjectionResource projection) slot = Some owner ->
    loopStateRequirements telescope slot = FixedResourceSubject expected ->
    projectionSubjectOf (loopProjectionResource projection) owner = expected \/
      succession
        (projectionSubjectOf (loopProjectionResource projection) owner)
        expected.
Proof.
  intros succession telescope projection slot owner expected
    Haccepted Hdeclared Hbound Hrequirement.
  destruct Haccepted as [Hresource [_ Hrequirements]].
  pose proof (Hrequirements slot Hdeclared) as HprojectionRequirement.
  rewrite Hrequirement in HprojectionRequirement.
  eapply successful_fixed_slot_is_subject_justified.
  - exact Hresource.
  - exact Hbound.
  - exact HprojectionRequirement.
Qed.

(* Explicit propositional state transport. *)

Definition StateIndex : Type := nat.

Parameter AcceptedEqualityEvidence : StateIndex -> StateIndex -> Prop.

Definition CheckedStateTransport
  (source target : StateIndex) : Prop :=
  source = target \/ AcceptedEqualityEvidence source target.

Theorem definitional_state_transport_needs_no_extra_evidence :
  forall index,
    CheckedStateTransport index index.
Proof.
  intro index.
  unfold CheckedStateTransport.
  left.
  reflexivity.
Qed.

Theorem explicit_equality_evidence_admits_state_transport :
  forall source target,
    AcceptedEqualityEvidence source target ->
    CheckedStateTransport source target.
Proof.
  intros source target Hevidence.
  unfold CheckedStateTransport.
  right.
  exact Hevidence.
Qed.

Theorem nondefinitional_state_transport_requires_explicit_evidence :
  forall source target,
    source <> target ->
    CheckedStateTransport source target ->
    AcceptedEqualityEvidence source target.
Proof.
  intros source target Hdifferent Htransport.
  unfold CheckedStateTransport in Htransport.
  destruct Htransport as [Hequal | Hevidence].
  - exfalso.
    apply Hdifferent.
    exact Hequal.
  - exact Hevidence.
Qed.

Theorem implicit_nondefinitional_state_rewrite_rejects :
  forall source target,
    source <> target ->
    ~ AcceptedEqualityEvidence source target ->
    ~ CheckedStateTransport source target.
Proof.
  intros source target Hdifferent HnoEvidence Htransport.
  apply HnoEvidence.
  eapply nondefinitional_state_transport_requires_explicit_evidence.
  - exact Hdifferent.
  - exact Htransport.
Qed.

(*
  Partial-correctness boundary: this file contains no termination theorem.
  Re-entry preservation is conditional on each admitted initial/backedge
  projection and any explicit transport evidence supplied for that edge.
*)
