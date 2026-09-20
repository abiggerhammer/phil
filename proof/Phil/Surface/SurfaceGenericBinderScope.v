From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import BindingSemantics.
From Phil.Surface Require Import SurfaceBinderScopeCore.

(*
  Second bounded Rocq tranche for PHIL-SURFACE-BINDER-SCOPE-001.

  This slice owns only generic-static binder identity and lookup at the
  Grammar-v1 Surface boundary.  It does not reinterpret generic kinds,
  instantiate generic arguments, or duplicate effect-polymorphism semantics.

  Production GenericBinderScope constructs GenericStaticParameterKey values
  from one exact declaration root plus a monotonic telescope ordinal. Display
  spelling and source position remain diagnostic only.
*)

Definition SurfaceGenericDisplaySpelling := nat.
Definition SurfaceGenericSourcePosition := nat.

Inductive SurfaceGenericBinderKey : Type :=
| MkSurfaceGenericBinderKey :
    DeclarationIdentity -> nat -> SurfaceGenericBinderKey.

Definition surfaceGenericBinderRoot
  (key : SurfaceGenericBinderKey) : DeclarationIdentity :=
  match key with
  | MkSurfaceGenericBinderKey root _ => root
  end.

Definition surfaceGenericBinderOrdinal
  (key : SurfaceGenericBinderKey) : nat :=
  match key with
  | MkSurfaceGenericBinderKey _ ordinal => ordinal
  end.

Definition surfaceGenericBinderKey
  (declaration : DeclarationIdentity)
  (ordinal : nat)
  (_display : SurfaceGenericDisplaySpelling)
  (_position : SurfaceGenericSourcePosition)
  : SurfaceGenericBinderKey :=
  MkSurfaceGenericBinderKey declaration ordinal.

Theorem surface_generic_binder_identity_is_alpha_and_span_stable :
  forall declaration ordinal firstDisplay secondDisplay
         firstPosition secondPosition,
    surfaceGenericBinderKey
      declaration ordinal firstDisplay firstPosition =
    surfaceGenericBinderKey
      declaration ordinal secondDisplay secondPosition.
Proof.
  reflexivity.
Qed.

Theorem surface_generic_binder_key_preserves_exact_root :
  forall declaration ordinal display position,
    surfaceGenericBinderRoot
      (surfaceGenericBinderKey declaration ordinal display position) =
    declaration.
Proof.
  reflexivity.
Qed.

Theorem surface_generic_binder_key_preserves_exact_ordinal :
  forall declaration ordinal display position,
    surfaceGenericBinderOrdinal
      (surfaceGenericBinderKey declaration ordinal display position) =
    ordinal.
Proof.
  reflexivity.
Qed.

Theorem surface_generic_binder_distinct_ordinals_are_distinct :
  forall declaration firstOrdinal secondOrdinal
         firstDisplay secondDisplay firstPosition secondPosition,
    firstOrdinal <> secondOrdinal ->
    surfaceGenericBinderKey
      declaration firstOrdinal firstDisplay firstPosition <>
    surfaceGenericBinderKey
      declaration secondOrdinal secondDisplay secondPosition.
Proof.
  intros declaration firstOrdinal secondOrdinal
    firstDisplay secondDisplay firstPosition secondPosition
    Hordinal Heq.
  apply Hordinal.
  pose proof (f_equal surfaceGenericBinderOrdinal Heq) as Hprojected.
  exact Hprojected.
Qed.

Theorem surface_generic_binder_distinct_roots_are_distinct :
  forall firstRoot secondRoot ordinal
         firstDisplay secondDisplay firstPosition secondPosition,
    firstRoot <> secondRoot ->
    surfaceGenericBinderKey
      firstRoot ordinal firstDisplay firstPosition <>
    surfaceGenericBinderKey
      secondRoot ordinal secondDisplay secondPosition.
Proof.
  intros firstRoot secondRoot ordinal
    firstDisplay secondDisplay firstPosition secondPosition
    Hroot Heq.
  apply Hroot.
  pose proof (f_equal surfaceGenericBinderRoot Heq) as Hprojected.
  exact Hprojected.
Qed.

Inductive SurfaceGenericBinderAdmission : Type :=
| SurfaceGenericBinderAccepted :
    SurfaceGenericBinderKey -> SurfaceGenericBinderAdmission
| SurfaceGenericBinderDuplicateRejected.

Definition decideSurfaceGenericBinderAdmission
  (declaration : DeclarationIdentity)
  (ordinal : nat)
  (duplicate : bool)
  : SurfaceGenericBinderAdmission :=
  if duplicate
  then SurfaceGenericBinderDuplicateRejected
  else
    SurfaceGenericBinderAccepted
      (MkSurfaceGenericBinderKey declaration ordinal).

Theorem duplicate_surface_generic_binder_rejects :
  forall declaration ordinal,
    decideSurfaceGenericBinderAdmission declaration ordinal true =
      SurfaceGenericBinderDuplicateRejected.
Proof.
  reflexivity.
Qed.

Theorem accepted_surface_generic_binder_has_exact_identity :
  forall declaration ordinal,
    decideSurfaceGenericBinderAdmission declaration ordinal false =
      SurfaceGenericBinderAccepted
        (MkSurfaceGenericBinderKey declaration ordinal).
Proof.
  reflexivity.
Qed.

Inductive SurfaceGenericLookupDecision : Type :=
| SurfaceGenericLookupResolved :
    SurfaceGenericBinderKey -> SurfaceGenericLookupDecision
| SurfaceGenericLookupNotInScope.

Definition decideSurfaceGenericLookup
  (resolved : option SurfaceGenericBinderKey)
  : SurfaceGenericLookupDecision :=
  match resolved with
  | Some key => SurfaceGenericLookupResolved key
  | None => SurfaceGenericLookupNotInScope
  end.

Theorem surface_generic_lookup_returns_exact_semantic_parameter :
  forall key,
    decideSurfaceGenericLookup (Some key) =
      SurfaceGenericLookupResolved key.
Proof.
  reflexivity.
Qed.

Theorem absent_surface_generic_lookup_rejects :
  decideSurfaceGenericLookup None =
    SurfaceGenericLookupNotInScope.
Proof.
  reflexivity.
Qed.

Definition surfaceGenericNextOrdinal (ordinal : nat) : nat := S ordinal.

Theorem surface_generic_telescope_positions_are_fresh :
  forall declaration ordinal display position,
    surfaceGenericBinderKey declaration ordinal display position <>
    surfaceGenericBinderKey
      declaration
      (surfaceGenericNextOrdinal ordinal)
      display
      position.
Proof.
  intros declaration ordinal display position.
  apply
    (surface_generic_binder_distinct_ordinals_are_distinct
      declaration ordinal (surfaceGenericNextOrdinal ordinal)
      display display position position).
  unfold surfaceGenericNextOrdinal.
  induction ordinal as [|ordinal IH].
  - discriminate.
  - intro Heq.
    inversion Heq.
    apply IH.
    assumption.
Qed.

Inductive SurfaceBinderNamespaceIdentity : Type :=
| SurfaceTermNamespaceIdentity : BinderKey -> SurfaceBinderNamespaceIdentity
| SurfaceGenericNamespaceIdentity :
    SurfaceGenericBinderKey -> SurfaceBinderNamespaceIdentity.

Theorem term_and_generic_binder_namespaces_are_disjoint :
  forall termKey genericKey,
    SurfaceTermNamespaceIdentity termKey <>
    SurfaceGenericNamespaceIdentity genericKey.
Proof.
  discriminate.
Qed.

Record SurfaceGenericBinderScopeFacts : Type :=
  MkSurfaceGenericBinderScopeFacts {
    surfaceGenericIdentityExact : Prop;
    surfaceGenericAlphaStable : Prop;
    surfaceGenericDuplicateRejected : Prop;
    surfaceGenericTelescopeFresh : Prop;
    surfaceGenericLookupExact : Prop;
    surfaceGenericMissingLookupRejected : Prop;
    surfaceGenericNamespaceSeparateFromTerms : Prop
  }.

Definition SurfaceGenericBinderScopeValid
  (facts : SurfaceGenericBinderScopeFacts) : Prop :=
  surfaceGenericIdentityExact facts /\
  surfaceGenericAlphaStable facts /\
  surfaceGenericDuplicateRejected facts /\
  surfaceGenericTelescopeFresh facts /\
  surfaceGenericLookupExact facts /\
  surfaceGenericMissingLookupRejected facts /\
  surfaceGenericNamespaceSeparateFromTerms facts.

Theorem surface_generic_binder_scope_requires_all_authorities :
  forall facts,
    SurfaceGenericBinderScopeValid facts ->
    surfaceGenericIdentityExact facts /\
    surfaceGenericAlphaStable facts /\
    surfaceGenericDuplicateRejected facts /\
    surfaceGenericTelescopeFresh facts /\
    surfaceGenericLookupExact facts /\
    surfaceGenericMissingLookupRejected facts /\
    surfaceGenericNamespaceSeparateFromTerms facts.
Proof.
  intros facts H.
  exact H.
Qed.
