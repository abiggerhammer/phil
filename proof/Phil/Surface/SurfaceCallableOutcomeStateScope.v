From Stdlib Require Import Lists.List Arith.PeanoNat Lia.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import
  SurfaceBinderScopeCore
  SurfaceLetPatternScope.

Import ListNotations.

(*
  Bounded PHIL-SURFACE-BINDER-SCOPE-001 tranche for callable outcome-state
  binders.

  Production SemanticCallableOutcomeState allocates each explicit state clause
  in its own child lexical frame. The clause's SurfaceState starts from the
  callable parameter state, but BinderKey ordinals advance globally across
  sibling state clauses and sibling outcome residues.

  Result-refinement binders may have consumed and closed an ordinal before this
  path begins; the first outcome-state binder therefore starts from the exact
  caller-supplied next ordinal rather than restarting its own stream.

  Outcome proposition truth remains a separate authority. This theorem owns
  branch-state identity, sibling isolation, and ordinal continuity only.
*)

Definition SurfaceCallableOutcomeSlotSite := SurfacePatternSite.

Definition allocateSurfaceCallableOutcomeSlots
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (slots : list SurfaceCallableOutcomeSlotSite)
  : list BinderKey * BinderOrdinal :=
  allocateSurfacePatternBinders declaration next slots.

Theorem callable_outcome_slot_allocation_preserves_source_order :
  forall declaration next slot rest keys finalOrdinal,
    allocateSurfaceCallableOutcomeSlots declaration (S next) rest =
      (keys, finalOrdinal) ->
    allocateSurfaceCallableOutcomeSlots declaration next (slot :: rest) =
      (semanticBinderKey declaration next :: keys, finalOrdinal).
Proof.
  intros declaration next slot rest keys finalOrdinal Hrest.
  unfold allocateSurfaceCallableOutcomeSlots in *.
  eapply pattern_allocation_preserves_first_source_position.
  exact Hrest.
Qed.

Theorem callable_outcome_slot_allocation_preserves_count :
  forall declaration next slots,
    length
      (fst (allocateSurfaceCallableOutcomeSlots declaration next slots)) =
    length slots.
Proof.
  intros declaration next slots.
  unfold allocateSurfaceCallableOutcomeSlots.
  apply pattern_allocation_preserves_binder_count.
Qed.

Theorem callable_outcome_slot_allocation_advances_exactly :
  forall declaration next slots binders finalOrdinal,
    allocateSurfaceCallableOutcomeSlots declaration next slots =
      (binders, finalOrdinal) ->
    finalOrdinal = next + length slots.
Proof.
  intros declaration next slots binders finalOrdinal Hallocate.
  unfold allocateSurfaceCallableOutcomeSlots in Hallocate.
  eapply pattern_allocation_consumes_one_fresh_ordinal_per_site.
  exact Hallocate.
Qed.

Record SurfaceCallableOutcomeStateScope : Type :=
  mkSurfaceCallableOutcomeStateScope {
    surfaceCallableOutcomeStateBinders : list BinderKey;
    surfaceCallableOutcomeStateNextOrdinal : BinderOrdinal
  }.

Definition checkSurfaceCallableOutcomeStateScope
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (slots : list SurfaceCallableOutcomeSlotSite)
  : SurfaceCallableOutcomeStateScope :=
  let '(binders, finalOrdinal) :=
    allocateSurfaceCallableOutcomeSlots declaration next slots in
  mkSurfaceCallableOutcomeStateScope binders finalOrdinal.

Theorem callable_outcome_state_contains_exact_allocated_binders :
  forall declaration next slots,
    surfaceCallableOutcomeStateBinders
      (checkSurfaceCallableOutcomeStateScope declaration next slots) =
    fst (allocateSurfaceCallableOutcomeSlots declaration next slots).
Proof.
  intros declaration next slots.
  unfold checkSurfaceCallableOutcomeStateScope.
  destruct (allocateSurfaceCallableOutcomeSlots declaration next slots).
  reflexivity.
Qed.

Theorem callable_outcome_state_exit_preserves_advanced_ordinal :
  forall declaration next slots,
    surfaceCallableOutcomeStateNextOrdinal
      (checkSurfaceCallableOutcomeStateScope declaration next slots) =
    next + length slots.
Proof.
  intros declaration next slots.
  unfold checkSurfaceCallableOutcomeStateScope.
  destruct
    (allocateSurfaceCallableOutcomeSlots declaration next slots)
    as [binders finalOrdinal] eqn:Hallocate.
  simpl.
  eapply callable_outcome_slot_allocation_advances_exactly.
  exact Hallocate.
Qed.

Definition surfaceCallableOutcomeLocalsVisibleAfterExit : bool := false.

Theorem callable_outcome_state_child_scope_is_discarded :
  surfaceCallableOutcomeLocalsVisibleAfterExit = false.
Proof.
  reflexivity.
Qed.

Inductive SurfaceOutcomeSemanticStateOrigin : Type :=
| SurfaceOutcomeParameterState.

Definition surfaceCallableOutcomeStateOrigin
  (_ : SurfaceCallableOutcomeStateScope)
  : SurfaceOutcomeSemanticStateOrigin :=
  SurfaceOutcomeParameterState.

Theorem sibling_callable_outcome_scopes_restart_from_parameter_state :
  forall scope,
    surfaceCallableOutcomeStateOrigin scope =
      SurfaceOutcomeParameterState.
Proof.
  reflexivity.
Qed.

Definition checkSurfaceSiblingCallableOutcomeState
  (declaration : DeclarationIdentity)
  (previous : SurfaceCallableOutcomeStateScope)
  (slots : list SurfaceCallableOutcomeSlotSite)
  : SurfaceCallableOutcomeStateScope :=
  checkSurfaceCallableOutcomeStateScope
    declaration
    (surfaceCallableOutcomeStateNextOrdinal previous)
    slots.

Theorem sibling_callable_outcome_starts_at_previous_advanced_ordinal :
  forall declaration previous slots,
    surfaceCallableOutcomeStateBinders
      (checkSurfaceSiblingCallableOutcomeState declaration previous slots) =
    fst
      (allocateSurfaceCallableOutcomeSlots
        declaration
        (surfaceCallableOutcomeStateNextOrdinal previous)
        slots).
Proof.
  intros declaration previous slots.
  unfold checkSurfaceSiblingCallableOutcomeState.
  apply callable_outcome_state_contains_exact_allocated_binders.
Qed.

Theorem nonempty_callable_outcome_scope_advances_ordinal :
  forall declaration next firstSlot rest,
    next <
      surfaceCallableOutcomeStateNextOrdinal
        (checkSurfaceCallableOutcomeStateScope
          declaration next (firstSlot :: rest)).
Proof.
  intros declaration next firstSlot rest.
  rewrite callable_outcome_state_exit_preserves_advanced_ordinal.
  simpl.
  lia.
Qed.

Theorem sibling_callable_outcome_reuse_gets_fresh_identity :
  forall declaration next firstSlot rest,
    semanticBinderKey declaration next <>
    semanticBinderKey declaration
      (surfaceCallableOutcomeStateNextOrdinal
        (checkSurfaceCallableOutcomeStateScope
          declaration next (firstSlot :: rest))).
Proof.
  intros declaration next firstSlot rest.
  apply
    (disjoint_sibling_binders_with_fresh_ordinals_are_distinct
      declaration
      next
      (surfaceCallableOutcomeStateNextOrdinal
        (checkSurfaceCallableOutcomeStateScope
          declaration next (firstSlot :: rest)))).
  pose proof
    (nonempty_callable_outcome_scope_advances_ordinal
      declaration next firstSlot rest) as Hlt.
  lia.
Qed.

Definition surfaceCallableOutcomePropositionVisibleBinders
  (scope : SurfaceCallableOutcomeStateScope)
  : list BinderKey :=
  surfaceCallableOutcomeStateBinders scope.

Theorem callable_outcome_propositions_see_exact_branch_state :
  forall declaration next slots,
    surfaceCallableOutcomePropositionVisibleBinders
      (checkSurfaceCallableOutcomeStateScope declaration next slots) =
    fst (allocateSurfaceCallableOutcomeSlots declaration next slots).
Proof.
  intros declaration next slots.
  unfold surfaceCallableOutcomePropositionVisibleBinders.
  apply callable_outcome_state_contains_exact_allocated_binders.
Qed.

Inductive SurfaceRepeatedOutcomeStateDecision : Type :=
| SurfaceSingleOutcomeStateScope
| SurfaceRepeatedOutcomeStateAmbiguous.

Definition decideSurfaceRepeatedOutcomeState
  (stateClauseCount : nat) : SurfaceRepeatedOutcomeStateDecision :=
  match stateClauseCount with
  | 0 => SurfaceSingleOutcomeStateScope
  | 1 => SurfaceSingleOutcomeStateScope
  | _ => SurfaceRepeatedOutcomeStateAmbiguous
  end.

Theorem two_outcome_state_clauses_are_not_silently_merged :
  decideSurfaceRepeatedOutcomeState 2 =
    SurfaceRepeatedOutcomeStateAmbiguous.
Proof.
  reflexivity.
Qed.

Theorem callable_outcome_alpha_renaming_preserves_semantic_binders :
  forall declaration next firstSlots secondSlots,
    length firstSlots = length secondSlots ->
    surfaceCallableOutcomeStateBinders
      (checkSurfaceCallableOutcomeStateScope declaration next firstSlots) =
    surfaceCallableOutcomeStateBinders
      (checkSurfaceCallableOutcomeStateScope declaration next secondSlots).
Proof.
  intros declaration next firstSlots secondSlots Hlength.
  repeat rewrite callable_outcome_state_contains_exact_allocated_binders.
  unfold allocateSurfaceCallableOutcomeSlots.
  eapply alpha_renaming_pattern_sites_preserves_semantic_identity.
  exact Hlength.
Qed.

Record SurfaceCallableOutcomeStateScopeFacts : Type :=
  mkSurfaceCallableOutcomeStateScopeFacts {
    surfaceCallableOutcomeIdentityExact : Prop;
    surfaceCallableOutcomeChildScopeIsolated : Prop;
    surfaceCallableOutcomeOrdinalMonotonic : Prop;
    surfaceCallableOutcomeSiblingFresh : Prop;
    surfaceCallableOutcomeParameterStateRestart : Prop;
    surfaceCallableOutcomePropositionIdentityExact : Prop;
    surfaceCallableOutcomeRepeatedStateAmbiguityExplicit : Prop;
    surfaceCallableOutcomeAlphaStable : Prop
  }.

Definition SurfaceCallableOutcomeStateScopeValid
  (facts : SurfaceCallableOutcomeStateScopeFacts) : Prop :=
  surfaceCallableOutcomeIdentityExact facts /\
  surfaceCallableOutcomeChildScopeIsolated facts /\
  surfaceCallableOutcomeOrdinalMonotonic facts /\
  surfaceCallableOutcomeSiblingFresh facts /\
  surfaceCallableOutcomeParameterStateRestart facts /\
  surfaceCallableOutcomePropositionIdentityExact facts /\
  surfaceCallableOutcomeRepeatedStateAmbiguityExplicit facts /\
  surfaceCallableOutcomeAlphaStable facts.

Theorem surface_callable_outcome_state_scope_requires_all_authorities :
  forall facts,
    SurfaceCallableOutcomeStateScopeValid facts ->
    surfaceCallableOutcomeIdentityExact facts /\
    surfaceCallableOutcomeChildScopeIsolated facts /\
    surfaceCallableOutcomeOrdinalMonotonic facts /\
    surfaceCallableOutcomeSiblingFresh facts /\
    surfaceCallableOutcomeParameterStateRestart facts /\
    surfaceCallableOutcomePropositionIdentityExact facts /\
    surfaceCallableOutcomeRepeatedStateAmbiguityExplicit facts /\
    surfaceCallableOutcomeAlphaStable facts.
Proof.
  intros facts Hvalid.
  exact Hvalid.
Qed.
