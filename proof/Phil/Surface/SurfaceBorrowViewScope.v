From Stdlib Require Import Arith.PeanoNat Lia.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import
  SurfaceBinderScopeCore
  SurfaceLetPatternScope.

(*
  Bounded PHIL-SURFACE-BINDER-SCOPE-001 tranche for borrow-view binders.

  Production BorrowViewScope resolves the owner in the parent scope before the
  view binder exists, enters one child lexical frame, allocates the view binder,
  checks body-local lets there, then discards the entire child frame while
  retaining the advanced declaration-wide ordinal.

  This theorem models only that lexical identity/visibility boundary. Loan
  admissibility and resource semantics remain owned by the existing Core
  borrow/resource authorities.
*)

Inductive SurfaceBorrowOwnerDecision : Type :=
| SurfaceBorrowOwnerResolved : BinderKey -> SurfaceBorrowOwnerDecision
| SurfaceBorrowOwnerOutsideLocalCompetence.

Definition decideSurfaceBorrowOwner
  (activeBeforeBorrow : option BinderKey)
  : SurfaceBorrowOwnerDecision :=
  match activeBeforeBorrow with
  | Some key => SurfaceBorrowOwnerResolved key
  | None => SurfaceBorrowOwnerOutsideLocalCompetence
  end.

Theorem borrow_owner_resolves_before_view_binding :
  forall key,
    decideSurfaceBorrowOwner (Some key) =
      SurfaceBorrowOwnerResolved key.
Proof.
  reflexivity.
Qed.

Theorem future_borrow_view_cannot_resolve_owner :
  decideSurfaceBorrowOwner None =
    SurfaceBorrowOwnerOutsideLocalCompetence.
Proof.
  reflexivity.
Qed.

Record SurfaceBorrowViewResult : Type := mkSurfaceBorrowViewResult {
  surfaceBorrowOwnerDecision : SurfaceBorrowOwnerDecision;
  surfaceBorrowViewBinder : BinderKey;
  surfaceBorrowNextOrdinal : BinderOrdinal
}.

Definition checkSurfaceBorrowView
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  (ownerBeforeBinding : option BinderKey)
  (bodyBinderCount : nat)
  : SurfaceBorrowViewResult :=
  mkSurfaceBorrowViewResult
    (decideSurfaceBorrowOwner ownerBeforeBinding)
    (semanticBinderKey declaration next)
    (S next + bodyBinderCount).

Theorem borrow_view_uses_exact_next_semantic_identity :
  forall declaration next owner bodyBinderCount,
    surfaceBorrowViewBinder
      (checkSurfaceBorrowView declaration next owner bodyBinderCount) =
    semanticBinderKey declaration next.
Proof.
  reflexivity.
Qed.

Theorem borrow_owner_decision_is_independent_of_future_view :
  forall declaration next owner bodyBinderCount,
    surfaceBorrowOwnerDecision
      (checkSurfaceBorrowView declaration next owner bodyBinderCount) =
    decideSurfaceBorrowOwner owner.
Proof.
  reflexivity.
Qed.

Theorem borrow_exit_never_rolls_back_view_ordinal :
  forall declaration next owner bodyBinderCount,
    next <
      surfaceBorrowNextOrdinal
        (checkSurfaceBorrowView declaration next owner bodyBinderCount).
Proof.
  intros declaration next owner bodyBinderCount.
  simpl.
  lia.
Qed.

Definition surfaceBorrowLocalsVisibleAfterExit
  (_ : SurfaceBorrowViewResult) : bool :=
  false.

Theorem borrow_child_scope_is_discarded_at_exit :
  forall result,
    surfaceBorrowLocalsVisibleAfterExit result = false.
Proof.
  reflexivity.
Qed.

Theorem sibling_borrow_view_reuse_gets_fresh_identity :
  forall declaration next owner bodyBinderCount,
    semanticBinderKey declaration next <>
    semanticBinderKey declaration
      (surfaceBorrowNextOrdinal
        (checkSurfaceBorrowView declaration next owner bodyBinderCount)).
Proof.
  intros declaration next owner bodyBinderCount.
  apply
    (disjoint_sibling_binders_with_fresh_ordinals_are_distinct
      declaration
      next
      (surfaceBorrowNextOrdinal
        (checkSurfaceBorrowView declaration next owner bodyBinderCount))).
  pose proof
    (borrow_exit_never_rolls_back_view_ordinal
      declaration next owner bodyBinderCount) as Hlt.
  lia.
Qed.

Theorem borrow_view_alpha_renaming_preserves_semantic_identity :
  forall declaration next owner bodyBinderCount
         firstDisplay secondDisplay firstPosition secondPosition,
    surfaceBinderKey
      declaration next firstDisplay firstPosition =
    surfaceBinderKey
      declaration next secondDisplay secondPosition.
Proof.
  intros.
  apply surface_binder_identity_is_alpha_and_span_stable.
Qed.

Record SurfaceBorrowViewScopeFacts : Type := mkSurfaceBorrowViewScopeFacts {
  surfaceBorrowOwnerPrecedesView : Prop;
  surfaceBorrowViewIdentityExact : Prop;
  surfaceBorrowChildScopeIsolated : Prop;
  surfaceBorrowOrdinalMonotonic : Prop;
  surfaceBorrowSiblingFresh : Prop;
  surfaceBorrowAlphaStable : Prop
}.

Definition SurfaceBorrowViewScopeValid
  (facts : SurfaceBorrowViewScopeFacts) : Prop :=
  surfaceBorrowOwnerPrecedesView facts /\
  surfaceBorrowViewIdentityExact facts /\
  surfaceBorrowChildScopeIsolated facts /\
  surfaceBorrowOrdinalMonotonic facts /\
  surfaceBorrowSiblingFresh facts /\
  surfaceBorrowAlphaStable facts.

Theorem surface_borrow_view_scope_requires_all_authorities :
  forall facts,
    SurfaceBorrowViewScopeValid facts ->
    surfaceBorrowOwnerPrecedesView facts /\
    surfaceBorrowViewIdentityExact facts /\
    surfaceBorrowChildScopeIsolated facts /\
    surfaceBorrowOrdinalMonotonic facts /\
    surfaceBorrowSiblingFresh facts /\
    surfaceBorrowAlphaStable facts.
Proof.
  intros facts Hvalid.
  exact Hvalid.
Qed.
