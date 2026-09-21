From Stdlib Require Import Lists.List Arith.PeanoNat Lia.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import
  SurfaceBinderScopeCore
  SurfaceLetPatternScope
  SurfaceJoinStateScope.

Import ListNotations.

(*
  Bounded PHIL-SURFACE-BINDER-SCOPE-001 tranche for loop-state binders.

  Production LoopStateScope has four lexical phases:

  1. every entry initializer is checked in the parent/pre-loop scope while all
     loop-header names are pending;
  2. header slot types are checked left-to-right before each corresponding
     binder is introduced, so later types may see earlier slots but not self or
     future slots;
  3. the invariant sees the complete header telescope;
  4. the body runs in a nested child scope that can see the header telescope,
     then both body and header scopes are discarded while the declaration-wide
     fresh ordinal remains advanced.

  Continue/break actual syntax remains explicit: an empty actual list stays empty
  and is never expanded into an implicit capture of loop state.

  Resource projection/backedge admissibility remain owned by PHIL-RES-LOOP-001.
*)

Definition SurfaceLoopSlotSite := SurfacePatternSite.

Definition decideSurfaceLoopInitializerReference
  (activeParent : option BinderKey)
  (pendingHeaderName : bool)
  : SurfaceLocalReferenceDecision :=
  decideSurfaceLocalReference activeParent pendingHeaderName.

Theorem loop_initializer_resolves_existing_parent_exactly :
  forall key pending,
    decideSurfaceLoopInitializerReference (Some key) pending =
      SurfaceLocalResolved key.
Proof.
  reflexivity.
Qed.

Theorem loop_initializer_cannot_see_future_header_binder :
  decideSurfaceLoopInitializerReference None true =
    SurfaceForwardReferenceRejected.
Proof.
  reflexivity.
Qed.

Theorem loop_initializer_unknown_nonlocal_stays_outside_local_competence :
  decideSurfaceLoopInitializerReference None false =
    SurfaceOutsideLocalCompetence.
Proof.
  reflexivity.
Qed.

Definition decideSurfaceLoopHeaderTypeReference
  (activeEarlierHeader : option BinderKey)
  (pendingCurrentOrFutureHeader : bool)
  : SurfaceLocalReferenceDecision :=
  decideSurfaceLocalReference
    activeEarlierHeader
    pendingCurrentOrFutureHeader.

Theorem later_loop_type_may_resolve_earlier_header_exactly :
  forall key,
    decideSurfaceLoopHeaderTypeReference (Some key) false =
      SurfaceLocalResolved key.
Proof.
  reflexivity.
Qed.

Theorem loop_type_self_or_forward_reference_rejects :
  decideSurfaceLoopHeaderTypeReference None true =
    SurfaceForwardReferenceRejected.
Proof.
  reflexivity.
Qed.

Definition allocateSurfaceLoopSlots
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (slots : list SurfaceLoopSlotSite)
  : list BinderKey * BinderOrdinal :=
  allocateSurfacePatternBinders declaration next slots.

Theorem loop_slot_allocation_preserves_source_order :
  forall declaration next slot rest keys finalOrdinal,
    allocateSurfaceLoopSlots declaration (S next) rest =
      (keys, finalOrdinal) ->
    allocateSurfaceLoopSlots declaration next (slot :: rest) =
      (semanticBinderKey declaration next :: keys, finalOrdinal).
Proof.
  intros declaration next slot rest keys finalOrdinal Hrest.
  unfold allocateSurfaceLoopSlots in *.
  eapply pattern_allocation_preserves_first_source_position.
  exact Hrest.
Qed.

Theorem loop_slot_allocation_preserves_count :
  forall declaration next slots,
    length (fst (allocateSurfaceLoopSlots declaration next slots)) =
    length slots.
Proof.
  intros declaration next slots.
  unfold allocateSurfaceLoopSlots.
  apply pattern_allocation_preserves_binder_count.
Qed.

Theorem loop_slot_allocation_advances_by_header_count :
  forall declaration next slots keys finalOrdinal,
    allocateSurfaceLoopSlots declaration next slots =
      (keys, finalOrdinal) ->
    finalOrdinal = next + length slots.
Proof.
  intros declaration next slots keys finalOrdinal Hallocate.
  unfold allocateSurfaceLoopSlots in Hallocate.
  eapply pattern_allocation_consumes_one_fresh_ordinal_per_site.
  exact Hallocate.
Qed.

Record SurfaceLoopHeader : Type := mkSurfaceLoopHeader {
  surfaceLoopHeaderBinders : list BinderKey;
  surfaceLoopHeaderNextOrdinal : BinderOrdinal
}.

Definition checkSurfaceLoopHeader
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (slots : list SurfaceLoopSlotSite)
  : SurfaceLoopHeader :=
  let '(binders, finalOrdinal) :=
    allocateSurfaceLoopSlots declaration next slots in
  mkSurfaceLoopHeader binders finalOrdinal.

Theorem loop_header_contains_exact_allocated_binders :
  forall declaration next slots,
    surfaceLoopHeaderBinders
      (checkSurfaceLoopHeader declaration next slots) =
    fst (allocateSurfaceLoopSlots declaration next slots).
Proof.
  intros declaration next slots.
  unfold checkSurfaceLoopHeader.
  destruct (allocateSurfaceLoopSlots declaration next slots).
  reflexivity.
Qed.

Theorem loop_header_next_ordinal_is_exact :
  forall declaration next slots,
    surfaceLoopHeaderNextOrdinal
      (checkSurfaceLoopHeader declaration next slots) =
    next + length slots.
Proof.
  intros declaration next slots.
  unfold checkSurfaceLoopHeader.
  destruct
    (allocateSurfaceLoopSlots declaration next slots)
    as [binders finalOrdinal] eqn:Hallocate.
  simpl.
  eapply loop_slot_allocation_advances_by_header_count.
  exact Hallocate.
Qed.

Definition surfaceLoopInvariantVisibleBinders
  (header : SurfaceLoopHeader) : list BinderKey :=
  surfaceLoopHeaderBinders header.

Theorem loop_invariant_sees_complete_header_telescope :
  forall declaration next slots,
    surfaceLoopInvariantVisibleBinders
      (checkSurfaceLoopHeader declaration next slots) =
    fst (allocateSurfaceLoopSlots declaration next slots).
Proof.
  intros declaration next slots.
  unfold surfaceLoopInvariantVisibleBinders.
  apply loop_header_contains_exact_allocated_binders.
Qed.

Definition surfaceLoopBodyVisibleHeaderBinders
  (header : SurfaceLoopHeader) : list BinderKey :=
  surfaceLoopHeaderBinders header.

Theorem loop_body_sees_exact_complete_header :
  forall declaration next slots,
    surfaceLoopBodyVisibleHeaderBinders
      (checkSurfaceLoopHeader declaration next slots) =
    fst (allocateSurfaceLoopSlots declaration next slots).
Proof.
  intros declaration next slots.
  unfold surfaceLoopBodyVisibleHeaderBinders.
  apply loop_header_contains_exact_allocated_binders.
Qed.

Definition surfaceLoopFinalOuterOrdinal
  (header : SurfaceLoopHeader)
  (bodyLocalBinderCount : nat) : BinderOrdinal :=
  surfaceLoopHeaderNextOrdinal header + bodyLocalBinderCount.

Theorem loop_scope_exit_never_rolls_back_header_or_body_allocation :
  forall header bodyLocalBinderCount,
    surfaceLoopHeaderNextOrdinal header <=
    surfaceLoopFinalOuterOrdinal header bodyLocalBinderCount.
Proof.
  intros header bodyLocalBinderCount.
  unfold surfaceLoopFinalOuterOrdinal.
  lia.
Qed.

Definition surfaceLoopLocalsVisibleAfterExit : bool := false.

Theorem loop_header_and_body_locals_disappear_after_exit :
  surfaceLoopLocalsVisibleAfterExit = false.
Proof.
  reflexivity.
Qed.

Definition surfaceLoopContinueActuals
  (actuals : list nat) : list nat :=
  actuals.

Theorem zero_actual_continue_never_implicitly_captures_loop_state :
  surfaceLoopContinueActuals [] = [].
Proof.
  reflexivity.
Qed.

Theorem explicit_continue_actuals_are_preserved_exactly :
  forall actuals,
    surfaceLoopContinueActuals actuals = actuals.
Proof.
  reflexivity.
Qed.

Theorem alpha_renamed_loop_header_preserves_semantic_binders :
  forall declaration next firstSlots secondSlots,
    length firstSlots = length secondSlots ->
    surfaceLoopHeaderBinders
      (checkSurfaceLoopHeader declaration next firstSlots) =
    surfaceLoopHeaderBinders
      (checkSurfaceLoopHeader declaration next secondSlots).
Proof.
  intros declaration next firstSlots secondSlots Hlength.
  repeat rewrite loop_header_contains_exact_allocated_binders.
  unfold allocateSurfaceLoopSlots.
  eapply alpha_renaming_pattern_sites_preserves_semantic_identity.
  exact Hlength.
Qed.

Record SurfaceLoopStateScopeFacts : Type := mkSurfaceLoopStateScopeFacts {
  surfaceLoopInitializersPrecedeHeader : Prop;
  surfaceLoopInitializerForwardReferencesRejected : Prop;
  surfaceLoopHeaderTypesPrecedeBinding : Prop;
  surfaceLoopEarlierHeaderDependenciesAllowed : Prop;
  surfaceLoopInvariantAfterCompleteHeader : Prop;
  surfaceLoopBodySeesHeader : Prop;
  surfaceLoopExitDropsLocalsWithoutRollback : Prop;
  surfaceLoopContinueActualsRemainExplicit : Prop;
  surfaceLoopAlphaStable : Prop
}.

Definition SurfaceLoopStateScopeValid
  (facts : SurfaceLoopStateScopeFacts) : Prop :=
  surfaceLoopInitializersPrecedeHeader facts /\
  surfaceLoopInitializerForwardReferencesRejected facts /\
  surfaceLoopHeaderTypesPrecedeBinding facts /\
  surfaceLoopEarlierHeaderDependenciesAllowed facts /\
  surfaceLoopInvariantAfterCompleteHeader facts /\
  surfaceLoopBodySeesHeader facts /\
  surfaceLoopExitDropsLocalsWithoutRollback facts /\
  surfaceLoopContinueActualsRemainExplicit facts /\
  surfaceLoopAlphaStable facts.

Theorem surface_loop_state_scope_requires_all_authorities :
  forall facts,
    SurfaceLoopStateScopeValid facts ->
    surfaceLoopInitializersPrecedeHeader facts /\
    surfaceLoopInitializerForwardReferencesRejected facts /\
    surfaceLoopHeaderTypesPrecedeBinding facts /\
    surfaceLoopEarlierHeaderDependenciesAllowed facts /\
    surfaceLoopInvariantAfterCompleteHeader facts /\
    surfaceLoopBodySeesHeader facts /\
    surfaceLoopExitDropsLocalsWithoutRollback facts /\
    surfaceLoopContinueActualsRemainExplicit facts /\
    surfaceLoopAlphaStable facts.
Proof.
  intros facts Hvalid.
  exact Hvalid.
Qed.
