From Stdlib Require Import Lists.List Sorting.Permutation.
Import ListNotations.

From Phil.Core Require Import CallableRefinement.

(*
  PHIL-CALL-REC-001 — stabilized recursive callable contracts.

  The recursive hypothesis is deliberately a public projection. Private
  implementation revision/body facts do not occur in the stabilized lookup
  relation. Declaration order is nonsemantic; duplicate stable names are
  rejected before lookup; and lookup is gated by the exact public interface
  revision carried by the stabilized CallableRefinementSurface.
*)

Parameter NamedCallableKey PrivateRevision Effect : Type.

Record NamedCallableDefinition : Type := mkNamedCallableDefinition {
  definitionKey : NamedCallableKey;
  definitionPublicSurface : CallableRefinementSurface;
  definitionPrivateRevision : PrivateRevision;
  definitionCurrentEffects : list Effect
}.

Definition PublicCallableView : Type :=
  (NamedCallableKey * CallableRefinementSurface)%type.

Definition publicView (definition : NamedCallableDefinition) : PublicCallableView :=
  (definitionKey definition, definitionPublicSurface definition).

Definition publicViews (definitions : list NamedCallableDefinition)
  : list PublicCallableView :=
  map publicView definitions.

Definition StabilizedLookup
  (definitions : list NamedCallableDefinition)
  (key : NamedCallableKey)
  (surface : CallableRefinementSurface) : Prop :=
  In (key, surface) (publicViews definitions).

Definition StabilizationAccepted (definitions : list NamedCallableDefinition) : Prop :=
  NoDup (map definitionKey definitions).

Definition RecursiveLookup
  (definitions : list NamedCallableDefinition)
  (key : NamedCallableKey)
  (expectedRevision : nat)
  (surface : CallableRefinementSurface) : Prop :=
  StabilizedLookup definitions key surface /\
  surfaceInterfaceRevision surface = expectedRevision.

Definition rewritePrivate
  (revision : PrivateRevision)
  (effects : list Effect)
  (definition : NamedCallableDefinition) : NamedCallableDefinition :=
  mkNamedCallableDefinition
    (definitionKey definition)
    (definitionPublicSurface definition)
    revision
    effects.

Theorem stabilization_exports_public_surface_only :
  forall definitions key surface,
    StabilizedLookup definitions key surface ->
    In (key, surface) (publicViews definitions).
Proof.
  intros definitions key surface Hlookup.
  exact Hlookup.
Qed.

Lemma public_views_private_rewrite :
  forall definitions revision effects,
    publicViews (map (rewritePrivate revision effects) definitions) =
    publicViews definitions.
Proof.
  induction definitions as [| definition rest IH]; intros revision effects.
  - reflexivity.
  - destruct definition.
    simpl in *.
    rewrite IH.
    reflexivity.
Qed.

Theorem private_implementation_facts_do_not_change_recursive_hypothesis :
  forall definitions revision effects key surface,
    StabilizedLookup (map (rewritePrivate revision effects) definitions) key surface <->
    StabilizedLookup definitions key surface.
Proof.
  intros definitions revision effects key surface.
  unfold StabilizedLookup.
  rewrite public_views_private_rewrite.
  reflexivity.
Qed.

Theorem declaration_order_is_nonsemantic :
  forall first second key surface,
    Permutation first second ->
    (StabilizedLookup first key surface <->
     StabilizedLookup second key surface).
Proof.
  intros first second key surface Hperm.
  unfold StabilizedLookup, publicViews.
  pose proof (Permutation_map publicView Hperm) as Hviews.
  split; intro Hin.
  - eapply Permutation_in; eauto.
  - eapply Permutation_in.
    + apply Permutation_sym. exact Hviews.
    + exact Hin.
Qed.

Theorem accepted_group_has_unique_stable_names :
  forall definitions,
    StabilizationAccepted definitions ->
    NoDup (map definitionKey definitions).
Proof.
  intros definitions Haccepted.
  exact Haccepted.
Qed.

Theorem adjacent_duplicate_stable_identity_rejects :
  forall first second rest,
    definitionKey first = definitionKey second ->
    ~ StabilizationAccepted (first :: second :: rest).
Proof.
  intros first second rest Hsame Haccepted.
  unfold StabilizationAccepted in Haccepted.
  simpl in Haccepted.
  inversion Haccepted as [| key names Hnotin Htail].
  apply Hnotin.
  simpl.
  left.
  symmetry.
  exact Hsame.
Qed.

Theorem recursive_lookup_uses_exact_stabilized_revision :
  forall definitions key revision surface,
    RecursiveLookup definitions key revision surface ->
    surfaceInterfaceRevision surface = revision.
Proof.
  intros definitions key revision surface Hlookup.
  exact (proj2 Hlookup).
Qed.

Theorem stale_interface_revision_cannot_rebind :
  forall definitions key expected surface,
    StabilizedLookup definitions key surface ->
    surfaceInterfaceRevision surface <> expected ->
    ~ RecursiveLookup definitions key expected surface.
Proof.
  intros definitions key expected surface Hknown Hstale Hlookup.
  apply Hstale.
  exact (proj2 Hlookup).
Qed.

Definition KnownRecursiveTarget
  (definitions : list NamedCallableDefinition)
  (key : NamedCallableKey) : Prop :=
  exists surface, StabilizedLookup definitions key surface.

Theorem unknown_recursive_target_rejects :
  forall definitions key expected surface,
    ~ KnownRecursiveTarget definitions key ->
    ~ RecursiveLookup definitions key expected surface.
Proof.
  intros definitions key expected surface Hunknown Hlookup.
  apply Hunknown.
  exists surface.
  exact (proj1 Hlookup).
Qed.

Theorem recursive_hypothesis_does_not_expose_private_revision :
  forall definitions key surface,
    StabilizedLookup definitions key surface ->
    forall revision effects,
      StabilizedLookup
        (map (rewritePrivate revision effects) definitions)
        key surface.
Proof.
  intros definitions key surface Hlookup revision effects.
  apply (proj2
    (private_implementation_facts_do_not_change_recursive_hypothesis
      definitions revision effects key surface)).
  exact Hlookup.
Qed.

Theorem recursive_lookup_returns_public_callable_surface :
  forall definitions key expected surface,
    RecursiveLookup definitions key expected surface ->
    StabilizedLookup definitions key surface.
Proof.
  intros definitions key expected surface Hlookup.
  exact (proj1 Hlookup).
Qed.
