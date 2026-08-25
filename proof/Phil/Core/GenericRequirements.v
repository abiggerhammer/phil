From Stdlib Require Import Lists.List Bool.Bool.

Import ListNotations.

From Phil.Core Require Import GenericStructural.

(*
  PHIL-GEN-REQ-001 — stabilized public generic structural requirements.

  This proof is deliberately layered on PHIL-GEN-STRUCT-001 rather than
  restating Phil's weakening/contraction semantics.  A checked generic body
  induces a minimum structural requirement set.  Its published public contract
  must cover that minimum exactly componentwise, but may intentionally be
  stronger.  Once such a public contract is fixed, body evolution is permitted
  so long as the new induced minimum remains covered; body growth beyond the
  published contract fails closed.

  The concrete Haskell parameter-key maps, explicit-vs-implicit published-list
  normalization, duplicate/unknown-key diagnostics, and correspondence from
  GenericStructuralRequirements Set values to the two-bit proof model remain
  explicit implementation boundaries.
*)

Definition boolImplies (required available : bool) : bool :=
  orb (negb required) available.

Definition requirementsCover
  (published induced : GenericStructuralRequirements) : bool :=
  andb
    (boolImplies (requiresWeakening induced) (requiresWeakening published))
    (boolImplies (requiresContraction induced) (requiresContraction published)).

Definition publishStructuralRequirements
  (induced : GenericStructuralRequirements)
  (explicitPublished : option GenericStructuralRequirements)
  : option GenericStructuralRequirements :=
  match explicitPublished with
  | None => Some induced
  | Some published =>
      if requirementsCover published induced
      then Some published
      else None
  end.

Theorem implicit_public_contract_is_exact_inferred_minimum :
  forall induced,
    publishStructuralRequirements induced None = Some induced.
Proof.
  reflexivity.
Qed.

Theorem explicit_public_contract_is_preserved_when_it_covers_body :
  forall induced published,
    requirementsCover published induced = true ->
    publishStructuralRequirements induced (Some published) = Some published.
Proof.
  intros induced published Hcover.
  unfold publishStructuralRequirements.
  rewrite Hcover.
  reflexivity.
Qed.

Theorem published_contract_may_be_stronger_than_body :
  publishStructuralRequirements
    emptyRequirements
    (Some (mkRequirements true true)) =
  Some (mkRequirements true true).
Proof.
  reflexivity.
Qed.

Theorem body_evolution_within_stable_weakening_contract_is_accepted :
  publishStructuralRequirements
    emptyRequirements
    (Some (mkRequirements true false)) =
  publishStructuralRequirements
    (mkRequirements true false)
    (Some (mkRequirements true false)).
Proof.
  reflexivity.
Qed.

Theorem body_evolution_within_stable_full_contract_is_accepted :
  forall induced,
    publishStructuralRequirements induced (Some (mkRequirements true true)) =
    Some (mkRequirements true true).
Proof.
  intros [weakening contraction].
  destruct weakening, contraction; reflexivity.
Qed.

Theorem body_cannot_outgrow_published_weakening_contract :
  publishStructuralRequirements
    (mkRequirements false true)
    (Some (mkRequirements true false)) = None.
Proof.
  reflexivity.
Qed.

Theorem omitted_explicit_permission_is_semantically_empty :
  publishStructuralRequirements
    (mkRequirements true false)
    (Some emptyRequirements) = None.
Proof.
  reflexivity.
Qed.

Theorem published_contract_acceptance_means_componentwise_coverage :
  forall induced published,
    publishStructuralRequirements induced (Some published) = Some published ->
    requirementsCover published induced = true.
Proof.
  intros induced published Hpublish.
  unfold publishStructuralRequirements in Hpublish.
  destruct (requirementsCover published induced) eqn:Hcover;
    [ reflexivity | discriminate ].
Qed.

Theorem accepted_published_contract_contains_induced_weakening :
  forall induced published,
    publishStructuralRequirements induced (Some published) = Some published ->
    requiresWeakening induced = true ->
    requiresWeakening published = true.
Proof.
  intros [inducedWeakening inducedContraction]
         [publishedWeakening publishedContraction]
         Hpublish Hweakening.
  simpl in Hweakening.
  subst inducedWeakening.
  unfold publishStructuralRequirements, requirementsCover, boolImplies in Hpublish.
  simpl in Hpublish.
  destruct publishedWeakening; simpl in Hpublish; [reflexivity | discriminate].
Qed.

Theorem accepted_published_contract_contains_induced_contraction :
  forall induced published,
    publishStructuralRequirements induced (Some published) = Some published ->
    requiresContraction induced = true ->
    requiresContraction published = true.
Proof.
  intros [inducedWeakening inducedContraction]
         [publishedWeakening publishedContraction]
         Hpublish Hcontraction.
  simpl in Hcontraction.
  subst inducedContraction.
  unfold publishStructuralRequirements, requirementsCover, boolImplies in Hpublish.
  destruct inducedWeakening, publishedWeakening, publishedContraction;
    simpl in Hpublish; try discriminate; reflexivity.
Qed.

Theorem accepted_contract_remains_stable_across_covered_body_revision :
  forall original revised published,
    requirementsCover published original = true ->
    requirementsCover published revised = true ->
    publishStructuralRequirements original (Some published) =
    publishStructuralRequirements revised (Some published).
Proof.
  intros original revised published Horiginal Hrevised.
  unfold publishStructuralRequirements.
  rewrite Horiginal, Hrevised.
  reflexivity.
Qed.

Theorem structural_inference_order_independence_preserves_publication :
  forall first second,
    publishStructuralRequirements
      (inferGenericStructuralRequirements [first; second]) None =
    publishStructuralRequirements
      (inferGenericStructuralRequirements [second; first]) None.
Proof.
  intros first second.
  repeat rewrite implicit_public_contract_is_exact_inferred_minimum.
  f_equal.
  apply two_use_inference_is_order_independent.
Qed.

Theorem unrestricted_actual_satisfies_any_accepted_public_contract :
  forall induced published,
    publishStructuralRequirements induced (Some published) = Some published ->
    modeSatisfiesRequirements Unrestricted published = true.
Proof.
  intros induced published _.
  apply unrestricted_satisfies_every_structural_requirement.
Qed.
