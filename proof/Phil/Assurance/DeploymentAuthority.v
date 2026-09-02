From Phil.Assurance Require Import DeploymentQualification.

(*
  PHIL-DEPLOY-AUTH-001 — qualification-gated narrow deployment authority
  (DEP-006).

  This model composes Certified PHIL-DEPLOY-QUAL-001.  A deployment
  qualification is necessary but never itself ambient authority: one explicit
  authority policy must select an exact deployment policy, exact qualified
  claim, exact action, and exact resource.  Grants remain content-bound to that
  policy and qualification and are revalidated against a current qualification
  at use time.

  Concrete Text/Map/Set representation, canonical hashing, secret-store/HSM/TEE
  enforcement, revocation/freshness truth, and toolchain correctness remain
  explicit correspondence/evidence boundaries.
*)

Definition DeploymentAuthorityPolicyRevision := nat.
Definition DeploymentAuthorityAction := nat.
Definition DeploymentAuthorityResource := nat.
Definition DeploymentAuthorityGrantId := nat.

Record DeploymentAuthorityPolicyModel : Type := mkDeploymentAuthorityPolicyModel {
  authorityPolicyRevision : DeploymentAuthorityPolicyRevision;
  authorityPolicyWellFormed : bool;
  authorityRequiredDeploymentPolicy : DeploymentPolicyId;
  authorityRequiredClaim : DeploymentClaimId;
  authorityAction : DeploymentAuthorityAction;
  authorityResource : DeploymentAuthorityResource
}.

Record DeploymentAuthorityGrantModel : Type := mkDeploymentAuthorityGrantModel {
  authorityGrantIdentity : DeploymentAuthorityGrantId;
  authorityGrantIdentityValid : bool;
  authorityGrantPolicyRevision : DeploymentAuthorityPolicyRevision;
  authorityGrantQualificationId : DeploymentQualificationId;
  authorityGrantClaim : DeploymentClaimId;
  authorityGrantAction : DeploymentAuthorityAction;
  authorityGrantResource : DeploymentAuthorityResource;
  authorityGrantValidFrom : DeploymentObservation;
  authorityGrantValidUntil : DeploymentObservation
}.

Record DeploymentAuthorityPolicyAdmissible
  (plan : DeploymentPlanModel)
  (qualification : DeploymentQualificationModel)
  (policy : DeploymentAuthorityPolicyModel) : Prop :=
  mkDeploymentAuthorityPolicyAdmissible {
    authorityPolicyIsWellFormed : authorityPolicyWellFormed policy = true;
    authorityDeploymentPolicyExact :
      authorityRequiredDeploymentPolicy policy = planPolicy plan;
    authorityClaimIsPlanned :
      planClaim plan (authorityRequiredClaim policy) = true;
    authorityClaimIsQualified :
      qualificationClaim qualification (authorityRequiredClaim policy) = true
  }.

Record DeploymentAuthorityGrantMatches
  (qualification : DeploymentQualificationModel)
  (policy : DeploymentAuthorityPolicyModel)
  (grant : DeploymentAuthorityGrantModel) : Prop :=
  mkDeploymentAuthorityGrantMatches {
    authorityGrantPolicyExact :
      authorityGrantPolicyRevision grant = authorityPolicyRevision policy;
    authorityGrantQualificationExact :
      authorityGrantQualificationId grant = qualificationIdentity qualification;
    authorityGrantClaimExact :
      authorityGrantClaim grant = authorityRequiredClaim policy;
    authorityGrantActionExact :
      authorityGrantAction grant = authorityAction policy;
    authorityGrantResourceExact :
      authorityGrantResource grant = authorityResource policy;
    authorityGrantValidityEndExact :
      authorityGrantValidUntil grant = qualificationValidUntil qualification;
    authorityGrantContentIdentityValid :
      authorityGrantIdentityValid grant = true
  }.

Record DeploymentAuthorityIssued
  (current : DeploymentObservation)
  (plan : DeploymentPlanModel)
  (domainRegistry : DeploymentDomainEvidenceRegistry)
  (compositionRegistry : DeploymentCompositionEvidenceRegistry)
  (qualification : DeploymentQualificationModel)
  (policy : DeploymentAuthorityPolicyModel)
  (grant : DeploymentAuthorityGrantModel) : Prop :=
  mkDeploymentAuthorityIssued {
    issuedQualificationValid :
      DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification;
    issuedPolicyAdmissible :
      DeploymentAuthorityPolicyAdmissible plan qualification policy;
    issuedGrantMatches :
      DeploymentAuthorityGrantMatches qualification policy grant;
    issuedGrantBeginsAtObservation :
      authorityGrantValidFrom grant = current
  }.

Record DeploymentAuthorityUsable
  (current : DeploymentObservation)
  (plan : DeploymentPlanModel)
  (domainRegistry : DeploymentDomainEvidenceRegistry)
  (compositionRegistry : DeploymentCompositionEvidenceRegistry)
  (qualification : DeploymentQualificationModel)
  (policy : DeploymentAuthorityPolicyModel)
  (grant : DeploymentAuthorityGrantModel) : Prop :=
  mkDeploymentAuthorityUsable {
    usableQualificationValid :
      DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification;
    usablePolicyAdmissible :
      DeploymentAuthorityPolicyAdmissible plan qualification policy;
    usableGrantMatches :
      DeploymentAuthorityGrantMatches qualification policy grant;
    usableGrantCurrent :
      PointWithin current
        (authorityGrantValidFrom grant)
        (authorityGrantValidUntil grant)
  }.

Definition DeploymentAuthorityAvailable
  (current : DeploymentObservation)
  (plan : DeploymentPlanModel)
  (domainRegistry : DeploymentDomainEvidenceRegistry)
  (compositionRegistry : DeploymentCompositionEvidenceRegistry)
  (maybeQualification : option DeploymentQualificationModel)
  (policy : DeploymentAuthorityPolicyModel) : Prop :=
  exists qualification grant,
    maybeQualification = Some qualification /\
    DeploymentAuthorityIssued
      current plan domainRegistry compositionRegistry qualification policy grant.

Theorem issued_deployment_authority_is_exactly_narrow :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    DeploymentAuthorityIssued
      current plan domainRegistry compositionRegistry qualification policy grant ->
    authorityGrantQualificationId grant = qualificationIdentity qualification /\
    authorityGrantClaim grant = authorityRequiredClaim policy /\
    authorityGrantAction grant = authorityAction policy /\
    authorityGrantResource grant = authorityResource policy /\
    authorityGrantValidFrom grant = current /\
    authorityGrantValidUntil grant = qualificationValidUntil qualification.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Hissued.
  pose proof
    (issuedGrantMatches
      current plan domainRegistry compositionRegistry qualification policy grant Hissued)
    as Hmatches.
  repeat split.
  - exact (authorityGrantQualificationExact qualification policy grant Hmatches).
  - exact (authorityGrantClaimExact qualification policy grant Hmatches).
  - exact (authorityGrantActionExact qualification policy grant Hmatches).
  - exact (authorityGrantResourceExact qualification policy grant Hmatches).
  - exact (issuedGrantBeginsAtObservation
      current plan domainRegistry compositionRegistry qualification policy grant Hissued).
  - exact (authorityGrantValidityEndExact qualification policy grant Hmatches).
Qed.

Theorem qualification_never_yields_ambient_authority :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    DeploymentAuthorityIssued
      current plan domainRegistry compositionRegistry qualification policy grant ->
    DeploymentAuthorityPolicyAdmissible plan qualification policy /\
    DeploymentAuthorityGrantMatches qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Hissued.
  split.
  - exact (issuedPolicyAdmissible
      current plan domainRegistry compositionRegistry qualification policy grant Hissued).
  - exact (issuedGrantMatches
      current plan domainRegistry compositionRegistry qualification policy grant Hissued).
Qed.

Theorem missing_qualification_cannot_produce_deployment_authority :
  forall current plan domainRegistry compositionRegistry policy,
    ~ DeploymentAuthorityAvailable
        current plan domainRegistry compositionRegistry None policy.
Proof.
  intros current plan domainRegistry compositionRegistry policy Havailable.
  destruct Havailable as [qualification Havailable].
  destruct Havailable as [grant Havailable].
  destruct Havailable as [Hpresent Hissued].
  discriminate Hpresent.
Qed.

Theorem stale_qualification_cannot_produce_deployment_authority :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    ~ PointWithin current
        (qualificationValidFrom qualification)
        (qualificationValidUntil qualification) ->
    ~ DeploymentAuthorityIssued
        current plan domainRegistry compositionRegistry qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Hstale Hissued.
  apply Hstale.
  exact (qualifiedCurrent
    current plan domainRegistry compositionRegistry qualification
    (issuedQualificationValid
      current plan domainRegistry compositionRegistry qualification policy grant Hissued)).
Qed.

Theorem wrong_deployment_policy_cannot_produce_authority :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    authorityRequiredDeploymentPolicy policy <> planPolicy plan ->
    ~ DeploymentAuthorityIssued
        current plan domainRegistry compositionRegistry qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Hwrong Hissued.
  apply Hwrong.
  exact (authorityDeploymentPolicyExact plan qualification policy
    (issuedPolicyAdmissible
      current plan domainRegistry compositionRegistry qualification policy grant Hissued)).
Qed.

Theorem unplanned_claim_cannot_produce_authority :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    planClaim plan (authorityRequiredClaim policy) = false ->
    ~ DeploymentAuthorityIssued
        current plan domainRegistry compositionRegistry qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Hunplanned Hissued.
  pose proof
    (authorityClaimIsPlanned plan qualification policy
      (issuedPolicyAdmissible
        current plan domainRegistry compositionRegistry qualification policy grant Hissued))
    as Hplanned.
  rewrite Hunplanned in Hplanned.
  discriminate.
Qed.

Theorem unqualified_claim_cannot_produce_authority :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    qualificationClaim qualification (authorityRequiredClaim policy) = false ->
    ~ DeploymentAuthorityIssued
        current plan domainRegistry compositionRegistry qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Hunqualified Hissued.
  pose proof
    (authorityClaimIsQualified plan qualification policy
      (issuedPolicyAdmissible
        current plan domainRegistry compositionRegistry qualification policy grant Hissued))
    as Hqualified.
  rewrite Hunqualified in Hqualified.
  discriminate.
Qed.

Theorem tampered_grant_action_cannot_be_used :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    authorityGrantAction grant <> authorityAction policy ->
    ~ DeploymentAuthorityUsable
        current plan domainRegistry compositionRegistry qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Htampered Husable.
  apply Htampered.
  exact (authorityGrantActionExact qualification policy grant
    (usableGrantMatches
      current plan domainRegistry compositionRegistry qualification policy grant Husable)).
Qed.

Theorem tampered_grant_resource_cannot_be_used :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    authorityGrantResource grant <> authorityResource policy ->
    ~ DeploymentAuthorityUsable
        current plan domainRegistry compositionRegistry qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Htampered Husable.
  apply Htampered.
  exact (authorityGrantResourceExact qualification policy grant
    (usableGrantMatches
      current plan domainRegistry compositionRegistry qualification policy grant Husable)).
Qed.

Theorem stale_qualification_invalidates_previously_issued_authority :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    ~ PointWithin current
        (qualificationValidFrom qualification)
        (qualificationValidUntil qualification) ->
    ~ DeploymentAuthorityUsable
        current plan domainRegistry compositionRegistry qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Hstale Husable.
  apply Hstale.
  exact (qualifiedCurrent
    current plan domainRegistry compositionRegistry qualification
    (usableQualificationValid
      current plan domainRegistry compositionRegistry qualification policy grant Husable)).
Qed.

Theorem deployment_authority_cannot_outlive_qualification :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    DeploymentAuthorityUsable
      current plan domainRegistry compositionRegistry qualification policy grant ->
    authorityGrantValidUntil grant = qualificationValidUntil qualification.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Husable.
  exact (authorityGrantValidityEndExact qualification policy grant
    (usableGrantMatches
      current plan domainRegistry compositionRegistry qualification policy grant Husable)).
Qed.

Theorem deployment_authority_use_requires_current_grant :
  forall current plan domainRegistry compositionRegistry qualification policy grant,
    DeploymentAuthorityUsable
      current plan domainRegistry compositionRegistry qualification policy grant ->
    PointWithin current
      (authorityGrantValidFrom grant)
      (authorityGrantValidUntil grant).
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant Husable.
  exact (usableGrantCurrent
    current plan domainRegistry compositionRegistry qualification policy grant Husable).
Qed.
