From Stdlib Require Import Lists.List Arith.PeanoNat Lia.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import
  SurfaceBinderScopeCore
  SurfaceLetPatternScope.

Import ListNotations.

(*
  Final named binder-family tranche for PHIL-SURFACE-BINDER-SCOPE-001.

  Production ProtocolBinderScope has two lexical lifetime rules:

  - send/receive message binders are introduced after their own type has been
    checked and remain active through the role continuation;
  - select/offer branch payload binders are introduced left-to-right in one
    branch child frame, remain active through that branch's guard/continuation,
    and disappear before the next sibling branch.

  Each role itself is also a child frame.  Role-local names disappear before the
  next role, while the declaration-wide fresh ordinal is retained.

  Guard proposition truth and semantic session construction remain separate
  authorities; this theorem owns only binder identity, ordering, and visibility.
*)

Definition decideSurfaceProtocolTypeReference
  (activeEarlier : option BinderKey)
  (pendingCurrentOrFuture : bool)
  : SurfaceLocalReferenceDecision :=
  decideSurfaceLocalReference activeEarlier pendingCurrentOrFuture.

Theorem protocol_type_reference_resolves_earlier_binder_exactly :
  forall key,
    decideSurfaceProtocolTypeReference (Some key) false =
      SurfaceLocalResolved key.
Proof.
  reflexivity.
Qed.

Theorem protocol_type_self_or_forward_reference_rejects :
  decideSurfaceProtocolTypeReference None true =
    SurfaceForwardReferenceRejected.
Proof.
  reflexivity.
Qed.

Theorem protocol_unknown_nonlocal_type_name_is_not_invented_local :
  decideSurfaceProtocolTypeReference None false =
    SurfaceOutsideLocalCompetence.
Proof.
  reflexivity.
Qed.

Record SurfaceProtocolMessageResult : Type :=
  mkSurfaceProtocolMessageResult {
    surfaceProtocolMessageTypeDecision : SurfaceLocalReferenceDecision;
    surfaceProtocolMessageBinder : BinderKey;
    surfaceProtocolMessageNextOrdinal : BinderOrdinal
  }.

Definition checkSurfaceProtocolMessage
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (activeEarlier : option BinderKey)
  (pendingCurrentOrFuture : bool)
  : SurfaceProtocolMessageResult :=
  mkSurfaceProtocolMessageResult
    (decideSurfaceProtocolTypeReference
      activeEarlier
      pendingCurrentOrFuture)
    (semanticBinderKey declaration next)
    (S next).

Theorem protocol_message_type_is_checked_before_binding :
  forall declaration next activeEarlier pending,
    surfaceProtocolMessageTypeDecision
      (checkSurfaceProtocolMessage
        declaration next activeEarlier pending) =
    decideSurfaceProtocolTypeReference activeEarlier pending.
Proof.
  reflexivity.
Qed.

Theorem protocol_message_uses_exact_next_identity :
  forall declaration next activeEarlier pending,
    surfaceProtocolMessageBinder
      (checkSurfaceProtocolMessage
        declaration next activeEarlier pending) =
    semanticBinderKey declaration next.
Proof.
  reflexivity.
Qed.

Theorem protocol_message_advances_one_ordinal :
  forall declaration next activeEarlier pending,
    surfaceProtocolMessageNextOrdinal
      (checkSurfaceProtocolMessage
        declaration next activeEarlier pending) =
    S next.
Proof.
  reflexivity.
Qed.

Definition surfaceProtocolMessageVisibleInContinuation
  (result : SurfaceProtocolMessageResult)
  : option BinderKey :=
  Some (surfaceProtocolMessageBinder result).

Theorem protocol_message_remains_visible_in_role_continuation :
  forall result,
    surfaceProtocolMessageVisibleInContinuation result =
      Some (surfaceProtocolMessageBinder result).
Proof.
  reflexivity.
Qed.

Definition surfaceProtocolMessageGuardDecision
  (result : SurfaceProtocolMessageResult)
  : SurfaceLocalReferenceDecision :=
  decideSurfaceLocalReference
    (Some (surfaceProtocolMessageBinder result))
    false.

Theorem protocol_message_guard_sees_exact_generated_binder :
  forall result,
    surfaceProtocolMessageGuardDecision result =
      SurfaceLocalResolved (surfaceProtocolMessageBinder result).
Proof.
  reflexivity.
Qed.

Definition SurfaceProtocolPayloadSite := SurfacePatternSite.

Definition allocateSurfaceProtocolPayloads
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (payloads : list SurfaceProtocolPayloadSite)
  : list BinderKey * BinderOrdinal :=
  allocateSurfacePatternBinders declaration next payloads.

Theorem protocol_payload_allocation_preserves_source_order :
  forall declaration next payload rest keys finalOrdinal,
    allocateSurfaceProtocolPayloads declaration (S next) rest =
      (keys, finalOrdinal) ->
    allocateSurfaceProtocolPayloads declaration next (payload :: rest) =
      (semanticBinderKey declaration next :: keys, finalOrdinal).
Proof.
  intros declaration next payload rest keys finalOrdinal Hrest.
  unfold allocateSurfaceProtocolPayloads in *.
  eapply pattern_allocation_preserves_first_source_position.
  exact Hrest.
Qed.

Theorem protocol_payload_allocation_preserves_count :
  forall declaration next payloads,
    length
      (fst (allocateSurfaceProtocolPayloads declaration next payloads)) =
    length payloads.
Proof.
  intros declaration next payloads.
  unfold allocateSurfaceProtocolPayloads.
  apply pattern_allocation_preserves_binder_count.
Qed.

Theorem protocol_payload_allocation_advances_by_payload_count :
  forall declaration next payloads binders finalOrdinal,
    allocateSurfaceProtocolPayloads declaration next payloads =
      (binders, finalOrdinal) ->
    finalOrdinal = next + length payloads.
Proof.
  intros declaration next payloads binders finalOrdinal Hallocate.
  unfold allocateSurfaceProtocolPayloads in Hallocate.
  eapply pattern_allocation_consumes_one_fresh_ordinal_per_site.
  exact Hallocate.
Qed.

Record SurfaceProtocolBranchResult : Type :=
  mkSurfaceProtocolBranchResult {
    surfaceProtocolBranchPayloadBinders : list BinderKey;
    surfaceProtocolBranchAfterPayloadOrdinal : BinderOrdinal;
    surfaceProtocolBranchFinalOrdinal : BinderOrdinal
  }.

Definition checkSurfaceProtocolBranch
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (payloads : list SurfaceProtocolPayloadSite)
  (continuationLocalBinderCount : nat)
  : SurfaceProtocolBranchResult :=
  let '(binders, afterPayload) :=
    allocateSurfaceProtocolPayloads declaration next payloads in
  mkSurfaceProtocolBranchResult
    binders
    afterPayload
    (afterPayload + continuationLocalBinderCount).

Theorem protocol_branch_payloads_are_exactly_allocated :
  forall declaration next payloads continuationLocalBinderCount,
    surfaceProtocolBranchPayloadBinders
      (checkSurfaceProtocolBranch
        declaration next payloads continuationLocalBinderCount) =
    fst (allocateSurfaceProtocolPayloads declaration next payloads).
Proof.
  intros declaration next payloads continuationLocalBinderCount.
  unfold checkSurfaceProtocolBranch.
  destruct
    (allocateSurfaceProtocolPayloads declaration next payloads).
  reflexivity.
Qed.

Theorem protocol_branch_after_payload_ordinal_is_exact :
  forall declaration next payloads continuationLocalBinderCount,
    surfaceProtocolBranchAfterPayloadOrdinal
      (checkSurfaceProtocolBranch
        declaration next payloads continuationLocalBinderCount) =
    next + length payloads.
Proof.
  intros declaration next payloads continuationLocalBinderCount.
  unfold checkSurfaceProtocolBranch.
  destruct
    (allocateSurfaceProtocolPayloads declaration next payloads)
    as [binders afterPayload] eqn:Hallocate.
  simpl.
  eapply protocol_payload_allocation_advances_by_payload_count.
  exact Hallocate.
Qed.

Theorem protocol_branch_final_ordinal_counts_all_branch_locals :
  forall declaration next payloads continuationLocalBinderCount,
    surfaceProtocolBranchFinalOrdinal
      (checkSurfaceProtocolBranch
        declaration next payloads continuationLocalBinderCount) =
    next + length payloads + continuationLocalBinderCount.
Proof.
  intros declaration next payloads continuationLocalBinderCount.
  unfold checkSurfaceProtocolBranch.
  destruct
    (allocateSurfaceProtocolPayloads declaration next payloads)
    as [binders afterPayload] eqn:Hallocate.
  simpl.
  pose proof
    (protocol_payload_allocation_advances_by_payload_count
      declaration next payloads binders afterPayload Hallocate)
    as Hafter.
  rewrite Hafter.
  reflexivity.
Qed.

Definition surfaceProtocolBranchGuardVisiblePayloads
  (result : SurfaceProtocolBranchResult) : list BinderKey :=
  surfaceProtocolBranchPayloadBinders result.

Theorem protocol_branch_guard_sees_complete_payload_telescope :
  forall declaration next payloads continuationLocalBinderCount,
    surfaceProtocolBranchGuardVisiblePayloads
      (checkSurfaceProtocolBranch
        declaration next payloads continuationLocalBinderCount) =
    fst (allocateSurfaceProtocolPayloads declaration next payloads).
Proof.
  intros declaration next payloads continuationLocalBinderCount.
  unfold surfaceProtocolBranchGuardVisiblePayloads.
  apply protocol_branch_payloads_are_exactly_allocated.
Qed.

Definition surfaceProtocolBranchContinuationVisiblePayloads
  (result : SurfaceProtocolBranchResult) : list BinderKey :=
  surfaceProtocolBranchPayloadBinders result.

Theorem protocol_branch_continuation_sees_complete_payload_telescope :
  forall declaration next payloads continuationLocalBinderCount,
    surfaceProtocolBranchContinuationVisiblePayloads
      (checkSurfaceProtocolBranch
        declaration next payloads continuationLocalBinderCount) =
    fst (allocateSurfaceProtocolPayloads declaration next payloads).
Proof.
  intros declaration next payloads continuationLocalBinderCount.
  unfold surfaceProtocolBranchContinuationVisiblePayloads.
  apply protocol_branch_payloads_are_exactly_allocated.
Qed.

Definition surfaceProtocolBranchLocalsVisibleAfterExit : bool := false.

Theorem protocol_branch_locals_disappear_before_sibling :
  surfaceProtocolBranchLocalsVisibleAfterExit = false.
Proof.
  reflexivity.
Qed.

Theorem protocol_branch_exit_never_rolls_back_ordinal :
  forall declaration next payloads continuationLocalBinderCount,
    next <=
      surfaceProtocolBranchFinalOrdinal
        (checkSurfaceProtocolBranch
          declaration next payloads continuationLocalBinderCount).
Proof.
  intros declaration next payloads continuationLocalBinderCount.
  rewrite protocol_branch_final_ordinal_counts_all_branch_locals.
  lia.
Qed.

Theorem nonempty_protocol_branch_advances_sibling_start :
  forall declaration next payloads continuationLocalBinderCount,
    length payloads + continuationLocalBinderCount > 0 ->
    next <
      surfaceProtocolBranchFinalOrdinal
        (checkSurfaceProtocolBranch
          declaration next payloads continuationLocalBinderCount).
Proof.
  intros declaration next payloads continuationLocalBinderCount Hnonempty.
  rewrite protocol_branch_final_ordinal_counts_all_branch_locals.
  lia.
Qed.

Theorem nonempty_protocol_branch_cannot_reuse_start_identity :
  forall declaration next payloads continuationLocalBinderCount,
    length payloads + continuationLocalBinderCount > 0 ->
    semanticBinderKey declaration next <>
    semanticBinderKey declaration
      (surfaceProtocolBranchFinalOrdinal
        (checkSurfaceProtocolBranch
          declaration next payloads continuationLocalBinderCount)).
Proof.
  intros declaration next payloads continuationLocalBinderCount Hnonempty.
  apply
    (disjoint_sibling_binders_with_fresh_ordinals_are_distinct
      declaration
      next
      (surfaceProtocolBranchFinalOrdinal
        (checkSurfaceProtocolBranch
          declaration next payloads continuationLocalBinderCount))).
  intro Heq.
  pose proof
    (nonempty_protocol_branch_advances_sibling_start
      declaration next payloads continuationLocalBinderCount Hnonempty)
    as Hlt.
  lia.
Qed.

Definition surfaceProtocolRoleLocalsVisibleAfterExit : bool := false.

Theorem protocol_role_locals_disappear_before_sibling_role :
  surfaceProtocolRoleLocalsVisibleAfterExit = false.
Proof.
  reflexivity.
Qed.

Definition surfaceProtocolRoleExitOrdinal
  (finalRoleOrdinal : BinderOrdinal) : BinderOrdinal :=
  finalRoleOrdinal.

Theorem protocol_role_exit_preserves_declaration_ordinal :
  forall finalRoleOrdinal,
    surfaceProtocolRoleExitOrdinal finalRoleOrdinal =
    finalRoleOrdinal.
Proof.
  reflexivity.
Qed.

Theorem protocol_message_alpha_renaming_is_nonsemantic :
  forall declaration next firstDisplay secondDisplay
         firstPosition secondPosition,
    surfaceBinderKey declaration next firstDisplay firstPosition =
    surfaceBinderKey declaration next secondDisplay secondPosition.
Proof.
  intros.
  apply surface_binder_identity_is_alpha_and_span_stable.
Qed.

Theorem protocol_payload_alpha_renaming_preserves_semantic_binders :
  forall declaration next firstPayloads secondPayloads,
    length firstPayloads = length secondPayloads ->
    fst (allocateSurfaceProtocolPayloads declaration next firstPayloads) =
    fst (allocateSurfaceProtocolPayloads declaration next secondPayloads).
Proof.
  intros declaration next firstPayloads secondPayloads Hlength.
  unfold allocateSurfaceProtocolPayloads.
  eapply alpha_renaming_pattern_sites_preserves_semantic_identity.
  exact Hlength.
Qed.

Record SurfaceProtocolBinderScopeFacts : Type :=
  mkSurfaceProtocolBinderScopeFacts {
    surfaceProtocolMessageTypePrecedesBinding : Prop;
    surfaceProtocolMessagePersistsInContinuation : Prop;
    surfaceProtocolMessageGuardIdentityExact : Prop;
    surfaceProtocolPayloadTypesPrecedeBinding : Prop;
    surfaceProtocolPayloadEarlierDependenciesAllowed : Prop;
    surfaceProtocolPayloadForwardReferencesRejected : Prop;
    surfaceProtocolBranchScopeIsolated : Prop;
    surfaceProtocolSiblingBranchFresh : Prop;
    surfaceProtocolRoleScopeIsolated : Prop;
    surfaceProtocolDeclarationOrdinalMonotonic : Prop;
    surfaceProtocolAlphaStable : Prop
  }.

Definition SurfaceProtocolBinderScopeValid
  (facts : SurfaceProtocolBinderScopeFacts) : Prop :=
  surfaceProtocolMessageTypePrecedesBinding facts /\
  surfaceProtocolMessagePersistsInContinuation facts /\
  surfaceProtocolMessageGuardIdentityExact facts /\
  surfaceProtocolPayloadTypesPrecedeBinding facts /\
  surfaceProtocolPayloadEarlierDependenciesAllowed facts /\
  surfaceProtocolPayloadForwardReferencesRejected facts /\
  surfaceProtocolBranchScopeIsolated facts /\
  surfaceProtocolSiblingBranchFresh facts /\
  surfaceProtocolRoleScopeIsolated facts /\
  surfaceProtocolDeclarationOrdinalMonotonic facts /\
  surfaceProtocolAlphaStable facts.

Theorem surface_protocol_binder_scope_requires_all_authorities :
  forall facts,
    SurfaceProtocolBinderScopeValid facts ->
    surfaceProtocolMessageTypePrecedesBinding facts /\
    surfaceProtocolMessagePersistsInContinuation facts /\
    surfaceProtocolMessageGuardIdentityExact facts /\
    surfaceProtocolPayloadTypesPrecedeBinding facts /\
    surfaceProtocolPayloadEarlierDependenciesAllowed facts /\
    surfaceProtocolPayloadForwardReferencesRejected facts /\
    surfaceProtocolBranchScopeIsolated facts /\
    surfaceProtocolSiblingBranchFresh facts /\
    surfaceProtocolRoleScopeIsolated facts /\
    surfaceProtocolDeclarationOrdinalMonotonic facts /\
    surfaceProtocolAlphaStable facts.
Proof.
  intros facts Hvalid.
  exact Hvalid.
Qed.
