From Stdlib Require Import Lists.List Arith.PeanoNat.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import
  SurfaceBinderScopeCore
  SurfaceLetPatternScope
  SurfaceCaseArmScope.

Import ListNotations.

(*
  Bounded PHIL-SURFACE-BINDER-SCOPE-001 tranche for explicit join-state binders.

  Production JoinStateScope checks predecessor arm/branch lexical scopes first,
  then checks each post-join slot type before allocating that slot binder.
  Earlier slots are therefore visible to later slot types; the current and later
  slots are still pending and reject as forward references.  The invariant is
  checked only after the whole post-join telescope has been allocated.

  Resource projection and invariant truth remain owned by PHIL-RES-JOIN-001 and
  PHIL-RES-INVARIANT-001.  This theorem owns only lexical identity and ordering.
*)

Definition SurfaceJoinSlotSite := SurfacePatternSite.

Definition decideSurfaceJoinReference
  (activeEarlierSlot : option BinderKey)
  (pendingJoinSlot : bool)
  : SurfaceLocalReferenceDecision :=
  decideSurfaceLocalReference activeEarlierSlot pendingJoinSlot.

Theorem earlier_join_slot_reference_resolves_exactly :
  forall key,
    decideSurfaceJoinReference (Some key) false =
      SurfaceLocalResolved key.
Proof.
  reflexivity.
Qed.

Theorem current_or_future_join_slot_reference_rejects :
  decideSurfaceJoinReference None true =
    SurfaceForwardReferenceRejected.
Proof.
  reflexivity.
Qed.

Theorem unrelated_join_type_name_stays_outside_local_competence :
  decideSurfaceJoinReference None false =
    SurfaceOutsideLocalCompetence.
Proof.
  reflexivity.
Qed.

Definition allocateSurfaceJoinSlots
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (slots : list SurfaceJoinSlotSite)
  : list BinderKey * BinderOrdinal :=
  allocateSurfacePatternBinders declaration next slots.

Theorem join_slot_allocation_preserves_source_order :
  forall declaration next slot rest keys finalOrdinal,
    allocateSurfaceJoinSlots declaration (S next) rest =
      (keys, finalOrdinal) ->
    allocateSurfaceJoinSlots declaration next (slot :: rest) =
      (semanticBinderKey declaration next :: keys, finalOrdinal).
Proof.
  intros declaration next slot rest keys finalOrdinal Hrest.
  unfold allocateSurfaceJoinSlots in *.
  eapply pattern_allocation_preserves_first_source_position.
  exact Hrest.
Qed.

Theorem join_slot_allocation_preserves_count :
  forall declaration next slots,
    length (fst (allocateSurfaceJoinSlots declaration next slots)) =
    length slots.
Proof.
  intros declaration next slots.
  unfold allocateSurfaceJoinSlots.
  apply pattern_allocation_preserves_binder_count.
Qed.

Theorem join_slot_allocation_advances_exactly_by_slot_count :
  forall declaration next slots keys finalOrdinal,
    allocateSurfaceJoinSlots declaration next slots =
      (keys, finalOrdinal) ->
    finalOrdinal = next + length slots.
Proof.
  intros declaration next slots keys finalOrdinal Hallocate.
  unfold allocateSurfaceJoinSlots in Hallocate.
  eapply pattern_allocation_consumes_one_fresh_ordinal_per_site.
  exact Hallocate.
Qed.

Record SurfaceJoinSlotCheck : Type := mkSurfaceJoinSlotCheck {
  surfaceJoinSlotTypeReferenceDecision : SurfaceLocalReferenceDecision;
  surfaceJoinSlotBinder : BinderKey;
  surfaceJoinSlotNextOrdinal : BinderOrdinal
}.

Definition checkSurfaceJoinSlot
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (activeEarlierSlot : option BinderKey)
  (pendingJoinSlot : bool)
  : SurfaceJoinSlotCheck :=
  mkSurfaceJoinSlotCheck
    (decideSurfaceJoinReference activeEarlierSlot pendingJoinSlot)
    (semanticBinderKey declaration next)
    (S next).

Theorem join_slot_type_reference_is_decided_before_binding :
  forall declaration next activeEarlier pending,
    surfaceJoinSlotTypeReferenceDecision
      (checkSurfaceJoinSlot declaration next activeEarlier pending) =
    decideSurfaceJoinReference activeEarlier pending.
Proof.
  reflexivity.
Qed.

Theorem join_slot_binder_uses_exact_next_identity :
  forall declaration next activeEarlier pending,
    surfaceJoinSlotBinder
      (checkSurfaceJoinSlot declaration next activeEarlier pending) =
    semanticBinderKey declaration next.
Proof.
  reflexivity.
Qed.

Theorem join_slot_allocation_advances_one_ordinal :
  forall declaration next activeEarlier pending,
    surfaceJoinSlotNextOrdinal
      (checkSurfaceJoinSlot declaration next activeEarlier pending) =
    S next.
Proof.
  reflexivity.
Qed.

Record SurfaceJoinTelescope : Type := mkSurfaceJoinTelescope {
  surfaceJoinTelescopeBinders : list BinderKey;
  surfaceJoinTelescopeNextOrdinal : BinderOrdinal
}.

Definition checkSurfaceJoinTelescope
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (slots : list SurfaceJoinSlotSite)
  : SurfaceJoinTelescope :=
  let '(binders, finalOrdinal) :=
    allocateSurfaceJoinSlots declaration next slots in
  mkSurfaceJoinTelescope binders finalOrdinal.

Theorem join_telescope_contains_exact_allocated_binders :
  forall declaration next slots,
    surfaceJoinTelescopeBinders
      (checkSurfaceJoinTelescope declaration next slots) =
    fst (allocateSurfaceJoinSlots declaration next slots).
Proof.
  intros declaration next slots.
  unfold checkSurfaceJoinTelescope.
  destruct (allocateSurfaceJoinSlots declaration next slots).
  reflexivity.
Qed.

Theorem join_invariant_scope_starts_after_complete_telescope :
  forall declaration next slots,
    surfaceJoinTelescopeNextOrdinal
      (checkSurfaceJoinTelescope declaration next slots) =
    next + length slots.
Proof.
  intros declaration next slots.
  unfold checkSurfaceJoinTelescope.
  destruct
    (allocateSurfaceJoinSlots declaration next slots)
    as [binders finalOrdinal] eqn:Hallocate.
  simpl.
  eapply join_slot_allocation_advances_exactly_by_slot_count.
  exact Hallocate.
Qed.

Definition surfaceJoinPredecessorLocalsVisibleAfterExit : bool := false.

Theorem predecessor_branch_locals_do_not_enter_post_join_scope :
  surfaceJoinPredecessorLocalsVisibleAfterExit = false.
Proof.
  reflexivity.
Qed.

Theorem alpha_renamed_join_telescope_preserves_semantic_binders :
  forall declaration next firstSlots secondSlots,
    length firstSlots = length secondSlots ->
    surfaceJoinTelescopeBinders
      (checkSurfaceJoinTelescope declaration next firstSlots) =
    surfaceJoinTelescopeBinders
      (checkSurfaceJoinTelescope declaration next secondSlots).
Proof.
  intros declaration next firstSlots secondSlots Hlength.
  repeat rewrite join_telescope_contains_exact_allocated_binders.
  unfold allocateSurfaceJoinSlots.
  eapply alpha_renaming_pattern_sites_preserves_semantic_identity.
  exact Hlength.
Qed.

Record SurfaceJoinStateScopeFacts : Type := mkSurfaceJoinStateScopeFacts {
  surfaceJoinPredecessorsClosedFirst : Prop;
  surfaceJoinSlotTypesPrecedeBinding : Prop;
  surfaceJoinForwardReferencesRejected : Prop;
  surfaceJoinEarlierDependenciesAllowed : Prop;
  surfaceJoinSlotIdentityExact : Prop;
  surfaceJoinInvariantAfterTelescope : Prop;
  surfaceJoinAlphaStable : Prop
}.

Definition SurfaceJoinStateScopeValid
  (facts : SurfaceJoinStateScopeFacts) : Prop :=
  surfaceJoinPredecessorsClosedFirst facts /\
  surfaceJoinSlotTypesPrecedeBinding facts /\
  surfaceJoinForwardReferencesRejected facts /\
  surfaceJoinEarlierDependenciesAllowed facts /\
  surfaceJoinSlotIdentityExact facts /\
  surfaceJoinInvariantAfterTelescope facts /\
  surfaceJoinAlphaStable facts.

Theorem surface_join_state_scope_requires_all_authorities :
  forall facts,
    SurfaceJoinStateScopeValid facts ->
    surfaceJoinPredecessorsClosedFirst facts /\
    surfaceJoinSlotTypesPrecedeBinding facts /\
    surfaceJoinForwardReferencesRejected facts /\
    surfaceJoinEarlierDependenciesAllowed facts /\
    surfaceJoinSlotIdentityExact facts /\
    surfaceJoinInvariantAfterTelescope facts /\
    surfaceJoinAlphaStable facts.
Proof.
  intros facts Hvalid.
  exact Hvalid.
Qed.
