From Stdlib Require Import Bool.Bool.

Inductive ReviewR14Decision : Type :=
| ReviewR14Accepted
| ReviewR14Rejected.

Definition reviewR14ProviderFactsb
  (r13RepresentedMeaningsValid requiredDomainEqualsCandidate : bool) : bool :=
  r13RepresentedMeaningsValid &&
  requiredDomainEqualsCandidate.

Definition decideReviewR14Provider
  (r13RepresentedMeaningsValid requiredDomainEqualsCandidate : bool)
  : ReviewR14Decision :=
  if reviewR14ProviderFactsb
      r13RepresentedMeaningsValid requiredDomainEqualsCandidate
  then ReviewR14Accepted
  else ReviewR14Rejected.

Definition reviewR14AuthorityFactsb
  (r13RepresentedMeaningsValid requiredDomainEqualsCandidate
   relativeAuthorityEffectValid : bool) : bool :=
  reviewR14ProviderFactsb
      r13RepresentedMeaningsValid requiredDomainEqualsCandidate &&
  relativeAuthorityEffectValid.

Definition decideReviewR14Authority
  (r13RepresentedMeaningsValid requiredDomainEqualsCandidate
   relativeAuthorityEffectValid : bool)
  : ReviewR14Decision :=
  if reviewR14AuthorityFactsb
      r13RepresentedMeaningsValid
      requiredDomainEqualsCandidate
      relativeAuthorityEffectValid
  then ReviewR14Accepted
  else ReviewR14Rejected.

Theorem exact_provider_inventory_accepts :
  decideReviewR14Provider true true = ReviewR14Accepted.
Proof. reflexivity. Qed.

Theorem coordinated_provider_site_deletion_rejects :
  decideReviewR14Provider true false = ReviewR14Rejected.
Proof. reflexivity. Qed.

Theorem relative_provider_consistency_is_not_independent_completeness :
  decideReviewR14Provider true false = ReviewR14Rejected.
Proof. reflexivity. Qed.

Theorem authority_effect_stage_propagates_provider_inventory_failure :
  decideReviewR14Authority true false true = ReviewR14Rejected.
Proof. reflexivity. Qed.

Theorem authority_effect_stage_requires_r13_semantic_validity_too :
  decideReviewR14Authority false true true = ReviewR14Rejected.
Proof. reflexivity. Qed.

Theorem exact_authority_effect_inventory_accepts :
  decideReviewR14Authority true true true = ReviewR14Accepted.
Proof. reflexivity. Qed.
