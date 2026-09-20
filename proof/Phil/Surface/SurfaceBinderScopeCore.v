From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import BindingSemantics.

(*
  First bounded Rocq tranche for PHIL-SURFACE-BINDER-SCOPE-001.

  PHIL-EXEC-BIND-001 already owns the normalized lexical binder algebra:
  declaration-root + monotonic ordinal identity, duplicate rejection, active
  shadowing rejection, and fresh sibling identity.

  This Surface tranche does not create a second binder semantics.  It exposes
  the exact subset consumed by Grammar-v1 term-binder resolution and records the
  Surface-specific competence split between:
    - an active local binder;
    - a pending local name, which is a forward-reference error; and
    - a nonlocal name, which stays outside this bounded local resolver.

  Concrete Text/Map/SourceSpan traversal, the $phil.local Core-name encoding,
  parser AST traversal, and category-specific body traversal remain explicit
  implementation-correspondence boundaries.
*)

Definition SurfaceDisplaySpelling := nat.
Definition SurfaceSourcePosition := nat.

Definition surfaceBinderKey
  (declaration : DeclarationIdentity)
  (ordinal : BinderOrdinal)
  (_display : SurfaceDisplaySpelling)
  (_position : SurfaceSourcePosition) : BinderKey :=
  semanticBinderKey declaration ordinal.

Theorem surface_binder_identity_is_alpha_and_span_stable :
  forall declaration ordinal firstDisplay secondDisplay
         firstPosition secondPosition,
    surfaceBinderKey declaration ordinal firstDisplay firstPosition =
    surfaceBinderKey declaration ordinal secondDisplay secondPosition.
Proof.
  reflexivity.
Qed.

Theorem surface_binder_identity_agrees_with_exec_binding_authority :
  forall declaration ordinal display position,
    surfaceBinderKey declaration ordinal display position =
    semanticBinderKey declaration ordinal.
Proof.
  reflexivity.
Qed.

Definition decideSurfaceBinderAdmission
  (declaration : DeclarationIdentity)
  (ordinal : BinderOrdinal)
  (duplicateInCurrentFrame activeInOuterFrame : bool) : BinderAdmission :=
  decideBinderAdmission
    declaration ordinal duplicateInCurrentFrame activeInOuterFrame.

Theorem surface_duplicate_binder_rejects :
  forall declaration ordinal activeOuter,
    decideSurfaceBinderAdmission declaration ordinal true activeOuter =
      BinderDuplicateRejected.
Proof.
  exact duplicate_binder_rejects.
Qed.

Theorem surface_active_shadowing_rejects :
  forall declaration ordinal,
    decideSurfaceBinderAdmission declaration ordinal false true =
      BinderActiveShadowingRejected.
Proof.
  exact active_shadowing_rejects.
Qed.

Theorem surface_accepted_binder_has_exact_root_and_ordinal :
  forall declaration ordinal,
    decideSurfaceBinderAdmission declaration ordinal false false =
      BinderAccepted (semanticBinderKey declaration ordinal).
Proof.
  exact accepted_binder_has_exact_declaration_root_and_ordinal.
Qed.

Definition allocateSurfaceBinderOrdinal
  (next : BinderOrdinal) : BinderOrdinal * BinderOrdinal :=
  (next, S next).

Definition leaveSurfaceLexicalScope
  (next : BinderOrdinal) : BinderOrdinal :=
  next.

Theorem leaving_scope_does_not_rollback_fresh_identity :
  forall next,
    leaveSurfaceLexicalScope next = next.
Proof.
  reflexivity.
Qed.

Theorem sibling_scope_reuse_gets_fresh_semantic_identity :
  forall declaration next,
    semanticBinderKey declaration next <>
    semanticBinderKey declaration (S next).
Proof.
  intros declaration next.
  apply
    (disjoint_sibling_binders_with_fresh_ordinals_are_distinct
      declaration next (S next)).
  induction next as [|next IH].
  - discriminate.
  - intro Heq.
    inversion Heq as [Heq'].
    apply IH.
    exact Heq'.
Qed.

Theorem distinct_declaration_roots_separate_equal_ordinals :
  forall firstRoot secondRoot ordinal,
    firstRoot <> secondRoot ->
    semanticBinderKey firstRoot ordinal <>
    semanticBinderKey secondRoot ordinal.
Proof.
  intros firstRoot secondRoot ordinal Hroots Hkeys.
  unfold semanticBinderKey in Hkeys.
  apply Hroots.
  inversion Hkeys.
  reflexivity.
Qed.

Inductive SurfaceLocalReferenceDecision : Type :=
| SurfaceLocalResolved : BinderKey -> SurfaceLocalReferenceDecision
| SurfaceForwardReferenceRejected
| SurfaceOutsideLocalCompetence.

Definition decideSurfaceLocalReference
  (active : option BinderKey)
  (pendingLocal : bool) : SurfaceLocalReferenceDecision :=
  match active with
  | Some key => SurfaceLocalResolved key
  | None =>
      if pendingLocal
      then SurfaceForwardReferenceRejected
      else SurfaceOutsideLocalCompetence
  end.

Theorem active_surface_local_resolves_to_exact_binder :
  forall key pendingLocal,
    decideSurfaceLocalReference (Some key) pendingLocal =
      SurfaceLocalResolved key.
Proof.
  reflexivity.
Qed.

Theorem pending_surface_local_rejects_forward_reference :
  decideSurfaceLocalReference None true =
    SurfaceForwardReferenceRejected.
Proof.
  reflexivity.
Qed.

Theorem unknown_nonlocal_name_stays_outside_local_competence :
  decideSurfaceLocalReference None false =
    SurfaceOutsideLocalCompetence.
Proof.
  reflexivity.
Qed.

Record SurfaceTermBinderScopeFacts : Type := mkSurfaceTermBinderScopeFacts {
  surfaceTermIdentityExact : Prop;
  surfaceTermAlphaStable : Prop;
  surfaceTermDuplicateRejected : Prop;
  surfaceTermActiveShadowRejected : Prop;
  surfaceTermSiblingFresh : Prop;
  surfaceTermResolutionExact : Prop;
  surfaceTermUnknownNamesNotGuessed : Prop
}.

Definition SurfaceTermBinderScopeValid
  (facts : SurfaceTermBinderScopeFacts) : Prop :=
  surfaceTermIdentityExact facts /\
  surfaceTermAlphaStable facts /\
  surfaceTermDuplicateRejected facts /\
  surfaceTermActiveShadowRejected facts /\
  surfaceTermSiblingFresh facts /\
  surfaceTermResolutionExact facts /\
  surfaceTermUnknownNamesNotGuessed facts.

Theorem surface_term_binder_scope_core_requires_all_authorities :
  forall facts,
    SurfaceTermBinderScopeValid facts ->
    surfaceTermIdentityExact facts /\
    surfaceTermAlphaStable facts /\
    surfaceTermDuplicateRejected facts /\
    surfaceTermActiveShadowRejected facts /\
    surfaceTermSiblingFresh facts /\
    surfaceTermResolutionExact facts /\
    surfaceTermUnknownNamesNotGuessed facts.
Proof.
  intros facts H.
  exact H.
Qed.
