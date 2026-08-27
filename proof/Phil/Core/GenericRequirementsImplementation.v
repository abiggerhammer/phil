From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import
  GenericStructural
  GenericRequirements.

(*
  PHIL-GEN-REQ-IMPL-001 — executable GEN-004–006 publication decision.

  The certified PHIL-GEN-REQ-001 model already defines componentwise coverage
  and public structural-requirement publication.  This refinement layer adds
  only the exact diagnostic decision needed by production.  Acceptance is
  proved equivalent both to the certified requirementsCover predicate and to
  successful explicit publication of the same public contract.
*)

Inductive GenericRequirementsCoverageDecision : Type :=
| GenericRequirementsCoverageAccepted
| GenericRequirementsCoverageMissingWeakening
| GenericRequirementsCoverageMissingContraction.

Definition decideGenericRequirementsCoverage
  (published induced : GenericStructuralRequirements)
  : GenericRequirementsCoverageDecision :=
  if andb
      (requiresWeakening induced)
      (negb (requiresWeakening published))
  then GenericRequirementsCoverageMissingWeakening
  else if andb
      (requiresContraction induced)
      (negb (requiresContraction published))
  then GenericRequirementsCoverageMissingContraction
  else GenericRequirementsCoverageAccepted.

Theorem generic_requirements_decision_accept_iff_cover :
  forall published induced,
    decideGenericRequirementsCoverage published induced =
      GenericRequirementsCoverageAccepted <->
    requirementsCover published induced = true.
Proof.
  intros [publishedWeakening publishedContraction]
         [inducedWeakening inducedContraction].
  destruct publishedWeakening, publishedContraction,
           inducedWeakening, inducedContraction;
    cbn; split; intro H; try reflexivity; try discriminate.
Qed.

Theorem generic_requirements_decision_accept_iff_explicit_publication :
  forall published induced,
    decideGenericRequirementsCoverage published induced =
      GenericRequirementsCoverageAccepted <->
    publishStructuralRequirements induced (Some published) = Some published.
Proof.
  intros [publishedWeakening publishedContraction]
         [inducedWeakening inducedContraction].
  destruct publishedWeakening, publishedContraction,
           inducedWeakening, inducedContraction;
    cbn; split; intro H; try reflexivity; try discriminate.
Qed.

Theorem generic_requirements_missing_weakening_is_exact :
  forall published induced,
    decideGenericRequirementsCoverage published induced =
      GenericRequirementsCoverageMissingWeakening ->
    requiresWeakening induced = true /\
    requiresWeakening published = false.
Proof.
  intros [publishedWeakening publishedContraction]
         [inducedWeakening inducedContraction].
  destruct publishedWeakening, publishedContraction,
           inducedWeakening, inducedContraction;
    cbn; intro H; try discriminate; split; reflexivity.
Qed.

Theorem generic_requirements_missing_contraction_is_exact :
  forall published induced,
    decideGenericRequirementsCoverage published induced =
      GenericRequirementsCoverageMissingContraction ->
    requiresContraction induced = true /\
    requiresContraction published = false /\
    (requiresWeakening induced = false \/
      requiresWeakening published = true).
Proof.
  intros [publishedWeakening publishedContraction]
         [inducedWeakening inducedContraction].
  destruct publishedWeakening, publishedContraction,
           inducedWeakening, inducedContraction;
    cbn; intro H; try discriminate;
    repeat split; try reflexivity; try (left; reflexivity); try (right; reflexivity).
Qed.

Theorem extracted_implicit_publication_is_certified :
  forall induced,
    publishStructuralRequirements induced None = Some induced.
Proof.
  exact implicit_public_contract_is_exact_inferred_minimum.
Qed.

Theorem extracted_stable_publication_is_certified :
  forall original revised published,
    requirementsCover published original = true ->
    requirementsCover published revised = true ->
    publishStructuralRequirements original (Some published) =
    publishStructuralRequirements revised (Some published).
Proof.
  exact accepted_contract_remains_stable_across_covered_body_revision.
Qed.
