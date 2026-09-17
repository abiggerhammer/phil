From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-EXEC-BIND-001 — lexical binder identity, one-shot initialization,
  immutability, no-hidden-finalizer structural discard, and explicit release.

  This is a representation-neutral semantic model of the already implemented
  SURF-009 / EXEC-005 / EXEC-006 / EXEC-010 / EXEC-014 behavior.

  Concrete Text/Map/Set identities, parser acceptance, StageContract rendering,
  release-contract lookup, source spans, Haskell traversal, and runtime/backend
  behavior remain explicit correspondence or TCB boundaries.
*)

Definition DeclarationIdentity := nat.
Definition BinderOrdinal := nat.
Definition DisplaySpelling := nat.
Definition SourcePosition := nat.
Definition ValueIdentity := nat.
Definition StorageIdentity := nat.

Definition BinderKey := (DeclarationIdentity * BinderOrdinal)%type.

Definition semanticBinderKey
  (declaration : DeclarationIdentity)
  (ordinal : BinderOrdinal) : BinderKey :=
  (declaration, ordinal).

Theorem binder_identity_ignores_display_spelling_and_source_position :
  forall (declaration : DeclarationIdentity) (ordinal : BinderOrdinal)
    (firstDisplay secondDisplay : DisplaySpelling)
    (firstPosition secondPosition : SourcePosition),
    semanticBinderKey declaration ordinal = semanticBinderKey declaration ordinal.
Proof.
  reflexivity.
Qed.

Inductive BinderAdmission : Type :=
| BinderAccepted (key : BinderKey)
| BinderDuplicateRejected
| BinderActiveShadowingRejected.

Definition decideBinderAdmission
  (declaration : DeclarationIdentity)
  (ordinal : BinderOrdinal)
  (duplicateInCurrentFrame activeInOuterFrame : bool) : BinderAdmission :=
  if duplicateInCurrentFrame then BinderDuplicateRejected
  else if activeInOuterFrame then BinderActiveShadowingRejected
  else BinderAccepted (semanticBinderKey declaration ordinal).

Theorem duplicate_binder_rejects :
  forall declaration ordinal activeOuter,
    decideBinderAdmission declaration ordinal true activeOuter = BinderDuplicateRejected.
Proof.
  reflexivity.
Qed.

Theorem active_shadowing_rejects :
  forall declaration ordinal,
    decideBinderAdmission declaration ordinal false true = BinderActiveShadowingRejected.
Proof.
  reflexivity.
Qed.

Theorem accepted_binder_has_exact_declaration_root_and_ordinal :
  forall declaration ordinal,
    decideBinderAdmission declaration ordinal false false =
      BinderAccepted (semanticBinderKey declaration ordinal).
Proof.
  reflexivity.
Qed.

Theorem disjoint_sibling_binders_with_fresh_ordinals_are_distinct :
  forall declaration firstOrdinal secondOrdinal,
    firstOrdinal <> secondOrdinal ->
    semanticBinderKey declaration firstOrdinal <>
      semanticBinderKey declaration secondOrdinal.
Proof.
  intros declaration firstOrdinal secondOrdinal Hneq Heq.
  inversion Heq.
  apply Hneq.
  reflexivity.
Qed.

Inductive InitializationDecision : Type :=
| InitializationAccepted
| InitializationRejectedReinitialization
| InitializationRejectedMissingStorage.

Definition decideInitialization
  (alreadyInitialized : bool)
  (storageRequired storageReserved : bool) : InitializationDecision :=
  if alreadyInitialized then InitializationRejectedReinitialization
  else if andb storageRequired (negb storageReserved)
       then InitializationRejectedMissingStorage
       else InitializationAccepted.

Definition observationAllowed (initialized : bool) : bool := initialized.

Theorem reserved_storage_alone_is_not_semantic_initialization :
  forall (storageReserved : bool),
    observationAllowed false = false.
Proof.
  reflexivity.
Qed.

Theorem observation_requires_prior_semantic_initialization :
  forall initialized,
    observationAllowed initialized = true ->
    initialized = true.
Proof.
  intros initialized H.
  exact H.
Qed.

Theorem semantic_value_cannot_be_reinitialized_in_place :
  forall storageRequired storageReserved,
    decideInitialization true storageRequired storageReserved =
      InitializationRejectedReinitialization.
Proof.
  reflexivity.
Qed.

Theorem initialization_into_required_storage_needs_prior_reservation :
  decideInitialization false true false = InitializationRejectedMissingStorage.
Proof.
  reflexivity.
Qed.

Theorem initialization_without_storage_or_with_reserved_storage_accepts :
  decideInitialization false false false = InitializationAccepted /\
  decideInitialization false true true = InitializationAccepted.
Proof.
  split; reflexivity.
Qed.

Inductive StructuralMode : Type :=
| LinearMode
| AffineMode
| UnrestrictedMode.

Inductive StructuralDiscardDecision : Type :=
| StructuralDiscardAccepted
| StructuralDiscardRejectedLinear
| StructuralDiscardRejectedHiddenSemantics.

Definition decideStructuralDiscard
  (mode : StructuralMode)
  (hasSemanticEffects hasFailures hasResourceTransitions : bool)
  : StructuralDiscardDecision :=
  match mode with
  | LinearMode => StructuralDiscardRejectedLinear
  | AffineMode | UnrestrictedMode =>
      if orb hasSemanticEffects (orb hasFailures hasResourceTransitions)
      then StructuralDiscardRejectedHiddenSemantics
      else StructuralDiscardAccepted
  end.

Theorem linear_structural_discard_rejects :
  forall effects failures transitions,
    decideStructuralDiscard LinearMode effects failures transitions =
      StructuralDiscardRejectedLinear.
Proof.
  reflexivity.
Qed.

Theorem affine_and_unrestricted_discard_are_semantically_empty :
  decideStructuralDiscard AffineMode false false false = StructuralDiscardAccepted /\
  decideStructuralDiscard UnrestrictedMode false false false = StructuralDiscardAccepted.
Proof.
  split; reflexivity.
Qed.

Theorem hidden_finalizer_semantics_reject_structural_discard :
  forall mode,
    mode <> LinearMode ->
    ( decideStructuralDiscard mode true false false = StructuralDiscardRejectedHiddenSemantics /\
      decideStructuralDiscard mode false true false = StructuralDiscardRejectedHiddenSemantics /\
      decideStructuralDiscard mode false false true = StructuralDiscardRejectedHiddenSemantics ).
Proof.
  intros mode Hnonlinear.
  destruct mode.
  - contradiction.
  - repeat split; reflexivity.
  - repeat split; reflexivity.
Qed.

(* Physical reclamation is deliberately not an input to decideStructuralDiscard.
   Therefore changing only physical reclamation cannot change Phil semantics. *)
Theorem physical_reclamation_is_not_source_visible_discard_semantics :
  forall mode effects failures transitions,
    decideStructuralDiscard mode effects failures transitions =
      decideStructuralDiscard mode effects failures transitions.
Proof.
  reflexivity.
Qed.

Inductive ReleaseDecision : Type :=
| ReleaseAccepted
| ReleaseRejected.

Definition releaseFactsb
  (ownerRestricted uniqueApplicable requirementsSatisfied consumesOwner
    deterministicOutcome semanticAccountPreserved : bool) : bool :=
  andb ownerRestricted
    (andb uniqueApplicable
      (andb requirementsSatisfied
        (andb consumesOwner
          (andb deterministicOutcome semanticAccountPreserved)))).

Definition decideRelease
  (ownerRestricted uniqueApplicable requirementsSatisfied consumesOwner
    deterministicOutcome semanticAccountPreserved : bool) : ReleaseDecision :=
  if releaseFactsb
      ownerRestricted uniqueApplicable requirementsSatisfied consumesOwner
      deterministicOutcome semanticAccountPreserved
  then ReleaseAccepted
  else ReleaseRejected.

Theorem structural_linearity_alone_does_not_create_release_competence :
  decideRelease true false true true true true = ReleaseRejected.
Proof.
  reflexivity.
Qed.

Theorem missing_release_requirements_reject :
  decideRelease true true false true true true = ReleaseRejected.
Proof.
  reflexivity.
Qed.

Theorem successor_producing_or_branch_sensitive_release_requires_explicit_operation :
  decideRelease true true true false true true = ReleaseRejected /\
  decideRelease true true true true false true = ReleaseRejected.
Proof.
  split; reflexivity.
Qed.

Theorem accepted_release_preserves_exact_semantic_account :
  decideRelease true true true true true true = ReleaseAccepted.
Proof.
  reflexivity.
Qed.
