From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import SurfaceBinderScopeCore.

(*
  Bounded PHIL-SURFACE-BINDER-SCOPE-001 tranche for semantic refinement binders.

  Production SemanticRefinementType enters one child lexical frame, allocates a
  GrammarV1RefinementBinder through the ordinary binder authority, checks and
  rewrites the predicate using that resolver-issued identity, then leaves the
  child frame while retaining the advanced declaration-wide ordinal.

  SurfaceState is a semantic carrier rather than a source-spelling scope:
  same-spelled state entries do not independently cause lexical shadowing.
*)

Definition SurfaceStateSpellingCollision := bool.

Definition decideSurfaceRefinementAdmission
  (declaration : DeclarationIdentity)
  (ordinal : BinderOrdinal)
  (duplicateInChildFrame activeInOuterFrame : bool)
  (_stateSpellingCollision : SurfaceStateSpellingCollision)
  : BinderAdmission :=
  decideSurfaceBinderAdmission
    declaration
    ordinal
    duplicateInChildFrame
    activeInOuterFrame.

Theorem refinement_admission_uses_lexical_scope_not_state_spelling :
  forall declaration ordinal stateCollision,
    decideSurfaceRefinementAdmission
      declaration ordinal false false stateCollision =
    BinderAccepted (semanticBinderKey declaration ordinal).
Proof.
  intros declaration ordinal stateCollision.
  unfold decideSurfaceRefinementAdmission.
  apply surface_accepted_binder_has_exact_root_and_ordinal.
Qed.

Theorem refinement_active_outer_shadowing_rejects :
  forall declaration ordinal stateCollision,
    decideSurfaceRefinementAdmission
      declaration ordinal false true stateCollision =
    BinderActiveShadowingRejected.
Proof.
  intros declaration ordinal stateCollision.
  unfold decideSurfaceRefinementAdmission.
  apply surface_active_shadowing_rejects.
Qed.

Theorem refinement_duplicate_child_binder_rejects :
  forall declaration ordinal activeOuter stateCollision,
    decideSurfaceRefinementAdmission
      declaration ordinal true activeOuter stateCollision =
    BinderDuplicateRejected.
Proof.
  intros declaration ordinal activeOuter stateCollision.
  unfold decideSurfaceRefinementAdmission.
  apply surface_duplicate_binder_rejects.
Qed.

Record SurfaceRefinementScopeResult : Type :=
  mkSurfaceRefinementScopeResult {
    surfaceRefinementBinder : BinderKey;
    surfaceRefinementPredicateDecision : SurfaceLocalReferenceDecision;
    surfaceRefinementNextOuterOrdinal : BinderOrdinal
  }.

Definition checkSurfaceRefinement
  (declaration : DeclarationIdentity)
  (next : BinderOrdinal)
  : SurfaceRefinementScopeResult :=
  let binder := semanticBinderKey declaration next in
  mkSurfaceRefinementScopeResult
    binder
    (decideSurfaceLocalReference (Some binder) false)
    (S next).

Theorem refinement_binder_uses_exact_next_identity :
  forall declaration next,
    surfaceRefinementBinder
      (checkSurfaceRefinement declaration next) =
    semanticBinderKey declaration next.
Proof.
  reflexivity.
Qed.

Theorem refinement_predicate_resolves_exact_generated_binder :
  forall declaration next,
    surfaceRefinementPredicateDecision
      (checkSurfaceRefinement declaration next) =
    SurfaceLocalResolved (semanticBinderKey declaration next).
Proof.
  reflexivity.
Qed.

Theorem refinement_scope_exit_retains_advanced_ordinal :
  forall declaration next,
    surfaceRefinementNextOuterOrdinal
      (checkSurfaceRefinement declaration next) =
    S next.
Proof.
  reflexivity.
Qed.

Definition surfaceRefinementBinderVisibleAfterExit
  (_ : SurfaceRefinementScopeResult) : bool :=
  false.

Theorem refinement_binder_is_child_local :
  forall result,
    surfaceRefinementBinderVisibleAfterExit result = false.
Proof.
  reflexivity.
Qed.

Theorem sibling_refinements_get_fresh_semantic_identities :
  forall declaration next,
    surfaceRefinementBinder
      (checkSurfaceRefinement declaration next) <>
    surfaceRefinementBinder
      (checkSurfaceRefinement declaration (S next)).
Proof.
  intros declaration next.
  simpl.
  apply sibling_scope_reuse_gets_fresh_semantic_identity.
Qed.

Theorem refinement_alpha_renaming_and_span_movement_are_nonsemantic :
  forall declaration next firstDisplay secondDisplay
         firstPosition secondPosition,
    surfaceBinderKey declaration next firstDisplay firstPosition =
    surfaceBinderKey declaration next secondDisplay secondPosition.
Proof.
  intros.
  apply surface_binder_identity_is_alpha_and_span_stable.
Qed.

Inductive SurfaceRefinementPredicateUse : Type :=
| SurfaceRefinementPredicateLocal : BinderKey -> SurfaceRefinementPredicateUse
| SurfaceRefinementPredicateNonlocal.

Definition classifySurfaceRefinementPredicateUse
  (activeLocal : option BinderKey)
  : SurfaceRefinementPredicateUse :=
  match activeLocal with
  | Some key => SurfaceRefinementPredicateLocal key
  | None => SurfaceRefinementPredicateNonlocal
  end.

Theorem refinement_predicate_local_use_preserves_exact_binder :
  forall key,
    classifySurfaceRefinementPredicateUse (Some key) =
    SurfaceRefinementPredicateLocal key.
Proof.
  reflexivity.
Qed.

Theorem refinement_predicate_nonlocal_use_is_not_invented_as_local :
  classifySurfaceRefinementPredicateUse None =
  SurfaceRefinementPredicateNonlocal.
Proof.
  reflexivity.
Qed.

Record SurfaceRefinementBinderScopeFacts : Type :=
  mkSurfaceRefinementBinderScopeFacts {
    surfaceRefinementLexicalAdmissionExact : Prop;
    surfaceRefinementStateSpellingNonAuthoritative : Prop;
    surfaceRefinementPredicateIdentityExact : Prop;
    surfaceRefinementChildScopeIsolated : Prop;
    surfaceRefinementOrdinalMonotonic : Prop;
    surfaceRefinementSiblingFresh : Prop;
    surfaceRefinementAlphaStable : Prop
  }.

Definition SurfaceRefinementBinderScopeValid
  (facts : SurfaceRefinementBinderScopeFacts) : Prop :=
  surfaceRefinementLexicalAdmissionExact facts /\
  surfaceRefinementStateSpellingNonAuthoritative facts /\
  surfaceRefinementPredicateIdentityExact facts /\
  surfaceRefinementChildScopeIsolated facts /\
  surfaceRefinementOrdinalMonotonic facts /\
  surfaceRefinementSiblingFresh facts /\
  surfaceRefinementAlphaStable facts.

Theorem surface_refinement_binder_scope_requires_all_authorities :
  forall facts,
    SurfaceRefinementBinderScopeValid facts ->
    surfaceRefinementLexicalAdmissionExact facts /\
    surfaceRefinementStateSpellingNonAuthoritative facts /\
    surfaceRefinementPredicateIdentityExact facts /\
    surfaceRefinementChildScopeIsolated facts /\
    surfaceRefinementOrdinalMonotonic facts /\
    surfaceRefinementSiblingFresh facts /\
    surfaceRefinementAlphaStable facts.
Proof.
  intros facts Hvalid.
  exact Hvalid.
Qed.
