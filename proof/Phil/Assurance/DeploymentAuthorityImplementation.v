From Stdlib Require Import Bool.Bool.

From Phil.Assurance Require Import DeploymentQualification DeploymentAuthority.

(*
  PHIL-DEPLOY-AUTH-001 — representation-neutral executable decision kernels
  for the Certified qualification-gated deployment authority relation.

  The already-Certified DeploymentQualificationValid predecessor is reflected
  as one Boolean fact at this boundary. Concrete Text/Map/Set representation,
  finite enumeration, canonical hashing, grant-id construction, diagnostics,
  provider enforcement, freshness/revocation truth, and extraction/toolchain
  correctness remain explicit native/evidence/TCB boundaries.
*)

Definition decideDeploymentAuthorityPolicyAdmissibleByFacts
  (policyWellFormed deploymentPolicyExact claimPlanned claimQualified : bool)
  : bool :=
  andb policyWellFormed
    (andb deploymentPolicyExact
      (andb claimPlanned claimQualified)).

Theorem deployment_authority_policy_decision_accept_iff_certified :
  forall plan qualification policy
         policyWellFormed deploymentPolicyExact claimPlanned claimQualified,
    (policyWellFormed = true <-> authorityPolicyWellFormed policy = true) ->
    (deploymentPolicyExact = true <->
      authorityRequiredDeploymentPolicy policy = planPolicy plan) ->
    (claimPlanned = true <->
      planClaim plan (authorityRequiredClaim policy) = true) ->
    (claimQualified = true <->
      qualificationClaim qualification (authorityRequiredClaim policy) = true) ->
    decideDeploymentAuthorityPolicyAdmissibleByFacts
      policyWellFormed deploymentPolicyExact claimPlanned claimQualified = true <->
    DeploymentAuthorityPolicyAdmissible plan qualification policy.
Proof.
  intros plan qualification policy
    policyWellFormed0 deploymentPolicyExact0 claimPlanned0 claimQualified0
    HwellFormed HdeploymentPolicy HclaimPlanned HclaimQualified.
  unfold decideDeploymentAuthorityPolicyAdmissibleByFacts.
  repeat rewrite andb_true_iff.
  rewrite HwellFormed, HdeploymentPolicy, HclaimPlanned, HclaimQualified.
  split.
  - intros [Hwf [Hpolicy [Hplanned Hqualified]]].
    constructor; assumption.
  - intros Hadmissible.
    repeat split.
    + exact (authorityPolicyIsWellFormed plan qualification policy Hadmissible).
    + exact (authorityDeploymentPolicyExact plan qualification policy Hadmissible).
    + exact (authorityClaimIsPlanned plan qualification policy Hadmissible).
    + exact (authorityClaimIsQualified plan qualification policy Hadmissible).
Qed.

Definition decideDeploymentAuthorityGrantMatchesByFacts
  (policyExact qualificationExact claimExact actionExact resourceExact
   validityEndExact contentIdentityValid : bool) : bool :=
  andb policyExact
    (andb qualificationExact
      (andb claimExact
        (andb actionExact
          (andb resourceExact
            (andb validityEndExact contentIdentityValid))))).

Theorem deployment_authority_grant_decision_accept_iff_certified :
  forall qualification policy grant
         policyExact qualificationExact claimExact actionExact resourceExact
         validityEndExact contentIdentityValid,
    (policyExact = true <->
      authorityGrantPolicyRevision grant = authorityPolicyRevision policy) ->
    (qualificationExact = true <->
      authorityGrantQualificationId grant = qualificationIdentity qualification) ->
    (claimExact = true <->
      authorityGrantClaim grant = authorityRequiredClaim policy) ->
    (actionExact = true <->
      authorityGrantAction grant = authorityAction policy) ->
    (resourceExact = true <->
      authorityGrantResource grant = authorityResource policy) ->
    (validityEndExact = true <->
      authorityGrantValidUntil grant = qualificationValidUntil qualification) ->
    (contentIdentityValid = true <->
      authorityGrantIdentityValid grant = true) ->
    decideDeploymentAuthorityGrantMatchesByFacts
      policyExact qualificationExact claimExact actionExact resourceExact
      validityEndExact contentIdentityValid = true <->
    DeploymentAuthorityGrantMatches qualification policy grant.
Proof.
  intros qualification policy grant
    policyExact0 qualificationExact0 claimExact0 actionExact0 resourceExact0
    validityEndExact0 contentIdentityValid0
    Hpolicy Hqualification Hclaim Haction Hresource Hend Hidentity.
  unfold decideDeploymentAuthorityGrantMatchesByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hpolicy, Hqualification, Hclaim, Haction, Hresource, Hend, Hidentity.
  split.
  - intros [Hpolicy0 [Hqualification0 [Hclaim0 [Haction0 [Hresource0 [Hend0 Hidentity0]]]]]].
    constructor; assumption.
  - intros Hmatches.
    repeat split.
    + exact (authorityGrantPolicyExact qualification policy grant Hmatches).
    + exact (authorityGrantQualificationExact qualification policy grant Hmatches).
    + exact (authorityGrantClaimExact qualification policy grant Hmatches).
    + exact (authorityGrantActionExact qualification policy grant Hmatches).
    + exact (authorityGrantResourceExact qualification policy grant Hmatches).
    + exact (authorityGrantValidityEndExact qualification policy grant Hmatches).
    + exact (authorityGrantContentIdentityValid qualification policy grant Hmatches).
Qed.

Definition decideDeploymentAuthorityIssuedByFacts
  (qualificationValid policyAdmissible grantMatches grantBeginsAtObservation : bool)
  : bool :=
  andb qualificationValid
    (andb policyAdmissible
      (andb grantMatches grantBeginsAtObservation)).

Theorem deployment_authority_issued_decision_accept_iff_certified :
  forall current plan domainRegistry compositionRegistry qualification policy grant
         qualificationValid policyAdmissible grantMatches grantBeginsAtObservation,
    (qualificationValid = true <->
      DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification) ->
    (policyAdmissible = true <->
      DeploymentAuthorityPolicyAdmissible plan qualification policy) ->
    (grantMatches = true <->
      DeploymentAuthorityGrantMatches qualification policy grant) ->
    (grantBeginsAtObservation = true <->
      authorityGrantValidFrom grant = current) ->
    decideDeploymentAuthorityIssuedByFacts
      qualificationValid policyAdmissible grantMatches grantBeginsAtObservation = true <->
    DeploymentAuthorityIssued
      current plan domainRegistry compositionRegistry qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant
    qualificationValid0 policyAdmissible0 grantMatches0 grantBeginsAtObservation0
    Hqualification Hpolicy Hgrant Hbegin.
  unfold decideDeploymentAuthorityIssuedByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hqualification, Hpolicy, Hgrant, Hbegin.
  split.
  - intros [Hqualification0 [Hpolicy0 [Hgrant0 Hbegin0]]].
    constructor; assumption.
  - intros Hissued.
    repeat split.
    + exact (issuedQualificationValid
        current plan domainRegistry compositionRegistry qualification policy grant Hissued).
    + exact (issuedPolicyAdmissible
        current plan domainRegistry compositionRegistry qualification policy grant Hissued).
    + exact (issuedGrantMatches
        current plan domainRegistry compositionRegistry qualification policy grant Hissued).
    + exact (issuedGrantBeginsAtObservation
        current plan domainRegistry compositionRegistry qualification policy grant Hissued).
Qed.

Definition decideDeploymentAuthorityUsableByFacts
  (qualificationValid policyAdmissible grantMatches grantCurrent : bool) : bool :=
  andb qualificationValid
    (andb policyAdmissible
      (andb grantMatches grantCurrent)).

Theorem deployment_authority_usable_decision_accept_iff_certified :
  forall current plan domainRegistry compositionRegistry qualification policy grant
         qualificationValid policyAdmissible grantMatches grantCurrent,
    (qualificationValid = true <->
      DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification) ->
    (policyAdmissible = true <->
      DeploymentAuthorityPolicyAdmissible plan qualification policy) ->
    (grantMatches = true <->
      DeploymentAuthorityGrantMatches qualification policy grant) ->
    (grantCurrent = true <->
      PointWithin current
        (authorityGrantValidFrom grant)
        (authorityGrantValidUntil grant)) ->
    decideDeploymentAuthorityUsableByFacts
      qualificationValid policyAdmissible grantMatches grantCurrent = true <->
    DeploymentAuthorityUsable
      current plan domainRegistry compositionRegistry qualification policy grant.
Proof.
  intros current plan domainRegistry compositionRegistry qualification policy grant
    qualificationValid0 policyAdmissible0 grantMatches0 grantCurrent0
    Hqualification Hpolicy Hgrant Hcurrent.
  unfold decideDeploymentAuthorityUsableByFacts.
  repeat rewrite andb_true_iff.
  rewrite Hqualification, Hpolicy, Hgrant, Hcurrent.
  split.
  - intros [Hqualification0 [Hpolicy0 [Hgrant0 Hcurrent0]]].
    constructor; assumption.
  - intros Husable.
    repeat split.
    + exact (usableQualificationValid
        current plan domainRegistry compositionRegistry qualification policy grant Husable).
    + exact (usablePolicyAdmissible
        current plan domainRegistry compositionRegistry qualification policy grant Husable).
    + exact (usableGrantMatches
        current plan domainRegistry compositionRegistry qualification policy grant Husable).
    + exact (usableGrantCurrent
        current plan domainRegistry compositionRegistry qualification policy grant Husable).
Qed.
