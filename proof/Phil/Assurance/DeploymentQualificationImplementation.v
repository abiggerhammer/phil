From Stdlib Require Import Bool.Bool.

From Phil.Assurance Require Import DeploymentQualification.

(*
  PHIL-DEPLOY-QUAL-001 — representation-neutral executable decision kernels
  for the Certified Deployment Qualification relation.

  Concrete Text/Map/Set representation, finite enumeration, canonical hashing,
  registry lookup, Integer/nat correspondence, diagnostic construction,
  attestation truth, wall-clock truth, and physical-topology truth stay native.
  Those checks reflect their exact semantic results into Booleans; the extracted
  kernel owns the final conjunction required by DeploymentQualificationValid.
*)

Definition decideDeploymentQualificationByFacts
  (topologyIdentityValid linksWellFormed claimDomainsTotal claimDomainsSound
   artifactExact policyExact topologyExact claimSetExact
   identityValidFact qualificationCurrent
   everySelectedDomainHasEvidence noExtraDomainBinding
   compositionEvidenceValid : bool) : bool :=
  andb topologyIdentityValid
    (andb linksWellFormed
      (andb claimDomainsTotal
        (andb claimDomainsSound
          (andb artifactExact
            (andb policyExact
              (andb topologyExact
                (andb claimSetExact
                  (andb identityValidFact
                    (andb qualificationCurrent
                      (andb everySelectedDomainHasEvidence
                        (andb noExtraDomainBinding compositionEvidenceValid))))))))))).

Theorem deployment_qualification_decision_accept_iff_certified :
  forall current plan domainRegistry compositionRegistry qualification
         topologyIdentityValid linksWellFormed claimDomainsTotal claimDomainsSound
         artifactExact policyExact topologyExact claimSetExact
         identityValidFact qualificationCurrent
         everySelectedDomainHasEvidence noExtraDomainBinding
         compositionEvidenceValid,
    (topologyIdentityValid = true <->
      planTopologyIdentityValid plan = true) ->
    (linksWellFormed = true <->
      planLinksWellFormed plan = true) ->
    (claimDomainsTotal = true <->
      forall claim,
        planClaim plan claim = true ->
        exists domain,
          planDomain plan domain = true /\
          planClaimDomain plan claim domain = true) ->
    (claimDomainsSound = true <->
      forall claim domain,
        planClaimDomain plan claim domain = true ->
        planClaim plan claim = true /\
        planDomain plan domain = true) ->
    (artifactExact = true <->
      qualificationArtifact qualification = planArtifact plan) ->
    (policyExact = true <->
      qualificationPolicy qualification = planPolicy plan) ->
    (topologyExact = true <->
      qualificationTopologyRevision qualification = planTopologyRevision plan) ->
    (claimSetExact = true <->
      forall claim,
        qualificationClaim qualification claim = planClaim plan claim) ->
    (identityValidFact = true <->
      qualificationIdentityValid qualification = true) ->
    (qualificationCurrent = true <->
      PointWithin current
        (qualificationValidFrom qualification)
        (qualificationValidUntil qualification)) ->
    (everySelectedDomainHasEvidence = true <->
      forall domain,
        planDomain plan domain = true ->
        exists key evidence,
          qualificationDomainEvidence qualification domain = Some key /\
          domainRegistry key = Some evidence /\
          domainEvidenceDomain evidence = domain /\
          domainEvidenceArtifact evidence = planArtifact plan /\
          domainEvidencePolicy evidence = planPolicy plan /\
          PointWithin current
            (domainEvidenceValidFrom evidence)
            (domainEvidenceValidUntil evidence) /\
          IntervalWithin
            (qualificationValidFrom qualification)
            (qualificationValidUntil qualification)
            (domainEvidenceValidFrom evidence)
            (domainEvidenceValidUntil evidence) /\
          (forall claim,
            planClaimDomain plan claim domain = true ->
            domainEvidenceClaim evidence claim = true)) ->
    (noExtraDomainBinding = true <->
      forall domain key,
        qualificationDomainEvidence qualification domain = Some key ->
        planDomain plan domain = true) ->
    (compositionEvidenceValid = true <->
      CompositeEvidenceRequirement
        current plan compositionRegistry qualification) ->
    decideDeploymentQualificationByFacts
      topologyIdentityValid linksWellFormed claimDomainsTotal claimDomainsSound
      artifactExact policyExact topologyExact claimSetExact
      identityValidFact qualificationCurrent
      everySelectedDomainHasEvidence noExtraDomainBinding
      compositionEvidenceValid = true <->
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification.
Proof.
  intros current plan domainRegistry compositionRegistry qualification
    topologyIdentityValid0 linksWellFormed0 claimDomainsTotal0 claimDomainsSound0
    artifactExact0 policyExact0 topologyExact0 claimSetExact0
    identityValidFact0 qualificationCurrent0
    everySelectedDomainHasEvidence0 noExtraDomainBinding0 compositionEvidenceValid0
    HtopologyIdentity HlinksWellFormed HclaimDomainsTotal HclaimDomainsSound
    HartifactExact HpolicyExact HtopologyExact HclaimSetExact
    HqualificationIdentity HqualificationCurrent
    HeverySelectedDomain HnoExtraDomain HcompositionEvidence.
  unfold decideDeploymentQualificationByFacts.
  repeat rewrite andb_true_iff.
  rewrite HtopologyIdentity, HlinksWellFormed, HclaimDomainsTotal,
          HclaimDomainsSound, HartifactExact, HpolicyExact, HtopologyExact,
          HclaimSetExact, HqualificationIdentity, HqualificationCurrent,
          HeverySelectedDomain, HnoExtraDomain, HcompositionEvidence.
  split.
  - intros Hfacts.
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    end.
    constructor; assumption.
  - intros Hvalid.
    destruct Hvalid.
    repeat (split; [assumption |]).
    assumption.
Qed.

Definition decideDeploymentQualificationAvailableByFacts
  (qualificationPresent qualificationValid : bool) : bool :=
  andb qualificationPresent qualificationValid.

Theorem deployment_qualification_available_decision_accept_iff_certified :
  forall current plan domainRegistry compositionRegistry maybeQualification
         qualificationPresent qualificationValid,
    (qualificationPresent = true <->
      exists qualification,
        maybeQualification = Some qualification) ->
    (qualificationValid = true <->
      forall qualification,
        maybeQualification = Some qualification ->
        DeploymentQualificationValid
          current plan domainRegistry compositionRegistry qualification) ->
    decideDeploymentQualificationAvailableByFacts
      qualificationPresent qualificationValid = true <->
    DeploymentQualificationAvailable
      current plan domainRegistry compositionRegistry maybeQualification.
Proof.
  intros current plan domainRegistry compositionRegistry maybeQualification
    qualificationPresent qualificationValid Hpresent Hvalid.
  unfold decideDeploymentQualificationAvailableByFacts,
         DeploymentQualificationAvailable.
  rewrite andb_true_iff, Hpresent, Hvalid.
  split.
  - intros Hfacts.
    destruct Hfacts as [[qualification Hqualification] HallValid].
    exists qualification.
    split.
    + exact Hqualification.
    + apply HallValid.
      exact Hqualification.
  - intros Havailable.
    destruct Havailable as [qualification [Hqualification HqualificationValid]].
    split.
    + exists qualification.
      exact Hqualification.
    + intros other Hother.
      rewrite Hqualification in Hother.
      injection Hother as Heq.
      rewrite <- Heq.
      exact HqualificationValid.
Qed.
