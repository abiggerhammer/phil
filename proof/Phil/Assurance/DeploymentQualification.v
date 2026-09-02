From Stdlib Require Import Arith.PeanoNat.

(*
  PHIL-DEPLOY-QUAL-001 — exact deployment qualification, freshness,
  and composite-topology integrity (DEP-003 through DEP-005).

  This normalized model captures the semantic contract implemented by
  Phil.Assurance.DeploymentQualification. Concrete Haskell Text/Map/Set
  representation, canonical hashing, registry enumeration, diagnostic payloads,
  attestation cryptography, platform roots of trust, wall-clock truth, and
  physical topology truth remain explicit correspondence/evidence boundaries.
*)

Definition DeploymentArtifactId := nat.
Definition DeploymentPolicyId := nat.
Definition DeploymentTopologyId := nat.
Definition DeploymentDomainId := nat.
Definition DeploymentLinkId := nat.
Definition DeploymentClaimId := nat.
Definition DeploymentEvidenceId := nat.
Definition DeploymentCompositionEvidenceId := nat.
Definition DeploymentQualificationId := nat.
Definition DeploymentObservation := nat.

Definition PointWithin
  (current validFrom validUntil : DeploymentObservation) : Prop :=
  validFrom <= current /\ current <= validUntil.

Definition IntervalWithin
  (innerFrom innerUntil outerFrom outerUntil : DeploymentObservation) : Prop :=
  outerFrom <= innerFrom /\ innerUntil <= outerUntil.

Record DeploymentPlanModel : Type := mkDeploymentPlanModel {
  planArtifact : DeploymentArtifactId;
  planPolicy : DeploymentPolicyId;
  planTopologyRevision : DeploymentTopologyId;
  planTopologyIdentityValid : bool;
  planLinksWellFormed : bool;
  planDomain : DeploymentDomainId -> bool;
  planLink : DeploymentLinkId -> bool;
  planClaim : DeploymentClaimId -> bool;
  planClaimDomain : DeploymentClaimId -> DeploymentDomainId -> bool;
  planComposite : bool
}.

Record DeploymentDomainEvidenceModel : Type := mkDeploymentDomainEvidenceModel {
  domainEvidenceArtifact : DeploymentArtifactId;
  domainEvidencePolicy : DeploymentPolicyId;
  domainEvidenceDomain : DeploymentDomainId;
  domainEvidenceValidFrom : DeploymentObservation;
  domainEvidenceValidUntil : DeploymentObservation;
  domainEvidenceClaim : DeploymentClaimId -> bool
}.

Record DeploymentCompositionEvidenceModel : Type := mkDeploymentCompositionEvidenceModel {
  compositionEvidenceArtifact : DeploymentArtifactId;
  compositionEvidencePolicy : DeploymentPolicyId;
  compositionEvidenceTopologyRevision : DeploymentTopologyId;
  compositionEvidenceValidFrom : DeploymentObservation;
  compositionEvidenceValidUntil : DeploymentObservation;
  compositionEvidenceDomain : DeploymentDomainId -> bool;
  compositionEvidenceLink : DeploymentLinkId -> bool;
  compositionEvidenceClaim : DeploymentClaimId -> bool
}.

Record DeploymentQualificationModel : Type := mkDeploymentQualificationModel {
  qualificationIdentity : DeploymentQualificationId;
  qualificationIdentityValid : bool;
  qualificationArtifact : DeploymentArtifactId;
  qualificationPolicy : DeploymentPolicyId;
  qualificationTopologyRevision : DeploymentTopologyId;
  qualificationClaim : DeploymentClaimId -> bool;
  qualificationDomainEvidence : DeploymentDomainId -> option DeploymentEvidenceId;
  qualificationCompositionEvidence : option DeploymentCompositionEvidenceId;
  qualificationValidFrom : DeploymentObservation;
  qualificationValidUntil : DeploymentObservation
}.

Definition DeploymentDomainEvidenceRegistry :=
  DeploymentEvidenceId -> option DeploymentDomainEvidenceModel.

Definition DeploymentCompositionEvidenceRegistry :=
  DeploymentCompositionEvidenceId -> option DeploymentCompositionEvidenceModel.

Definition CompositeEvidenceRequirement
  (current : DeploymentObservation)
  (plan : DeploymentPlanModel)
  (registry : DeploymentCompositionEvidenceRegistry)
  (qualification : DeploymentQualificationModel) : Prop :=
  match planComposite plan with
  | true =>
      exists key evidence,
        qualificationCompositionEvidence qualification = Some key /\
        registry key = Some evidence /\
        compositionEvidenceArtifact evidence = planArtifact plan /\
        compositionEvidencePolicy evidence = planPolicy plan /\
        compositionEvidenceTopologyRevision evidence = planTopologyRevision plan /\
        PointWithin current
          (compositionEvidenceValidFrom evidence)
          (compositionEvidenceValidUntil evidence) /\
        IntervalWithin
          (qualificationValidFrom qualification)
          (qualificationValidUntil qualification)
          (compositionEvidenceValidFrom evidence)
          (compositionEvidenceValidUntil evidence) /\
        (forall domain,
          compositionEvidenceDomain evidence domain = planDomain plan domain) /\
        (forall link,
          compositionEvidenceLink evidence link = planLink plan link) /\
        (forall claim,
          compositionEvidenceClaim evidence claim = planClaim plan claim)
  | false => qualificationCompositionEvidence qualification = None
  end.

Record DeploymentQualificationValid
  (current : DeploymentObservation)
  (plan : DeploymentPlanModel)
  (domainRegistry : DeploymentDomainEvidenceRegistry)
  (compositionRegistry : DeploymentCompositionEvidenceRegistry)
  (qualification : DeploymentQualificationModel) : Prop :=
  mkDeploymentQualificationValid {
    qualifiedTopologyIdentityValid : planTopologyIdentityValid plan = true;
    qualifiedLinksWellFormed : planLinksWellFormed plan = true;

    qualifiedClaimDomainsTotal :
      forall claim,
        planClaim plan claim = true ->
        exists domain,
          planDomain plan domain = true /\
          planClaimDomain plan claim domain = true;

    qualifiedClaimDomainsSound :
      forall claim domain,
        planClaimDomain plan claim domain = true ->
        planClaim plan claim = true /\
        planDomain plan domain = true;

    qualifiedExactArtifact :
      qualificationArtifact qualification = planArtifact plan;

    qualifiedExactPolicy :
      qualificationPolicy qualification = planPolicy plan;

    qualifiedExactTopology :
      qualificationTopologyRevision qualification = planTopologyRevision plan;

    qualifiedExactClaimSet :
      forall claim,
        qualificationClaim qualification claim = planClaim plan claim;

    qualifiedIdentityValid : qualificationIdentityValid qualification = true;

    qualifiedCurrent :
      PointWithin current
        (qualificationValidFrom qualification)
        (qualificationValidUntil qualification);

    qualifiedEverySelectedDomainHasEvidence :
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
            domainEvidenceClaim evidence claim = true);

    qualifiedNoExtraDomainBinding :
      forall domain key,
        qualificationDomainEvidence qualification domain = Some key ->
        planDomain plan domain = true;

    qualifiedCompositionEvidence :
      CompositeEvidenceRequirement
        current plan compositionRegistry qualification
  }.

Definition DeploymentQualificationAvailable
  (current : DeploymentObservation)
  (plan : DeploymentPlanModel)
  (domainRegistry : DeploymentDomainEvidenceRegistry)
  (compositionRegistry : DeploymentCompositionEvidenceRegistry)
  (maybeQualification : option DeploymentQualificationModel) : Prop :=
  exists qualification,
    maybeQualification = Some qualification /\
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification.

Theorem qualified_deployment_uses_exact_plan_identity :
  forall current plan domainRegistry compositionRegistry qualification,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
    qualificationArtifact qualification = planArtifact plan /\
    qualificationPolicy qualification = planPolicy plan /\
    qualificationTopologyRevision qualification = planTopologyRevision plan /\
    (forall claim,
      qualificationClaim qualification claim = planClaim plan claim) /\
    qualificationIdentityValid qualification = true.
Proof.
  intros current plan domainRegistry compositionRegistry qualification Hvalid.
  repeat split.
  - exact (qualifiedExactArtifact current plan domainRegistry compositionRegistry qualification Hvalid).
  - exact (qualifiedExactPolicy current plan domainRegistry compositionRegistry qualification Hvalid).
  - exact (qualifiedExactTopology current plan domainRegistry compositionRegistry qualification Hvalid).
  - exact (qualifiedExactClaimSet current plan domainRegistry compositionRegistry qualification Hvalid).
  - exact (qualifiedIdentityValid current plan domainRegistry compositionRegistry qualification Hvalid).
Qed.

Theorem raw_attestation_without_qualification_cannot_close :
  forall current plan domainRegistry compositionRegistry,
    ~ DeploymentQualificationAvailable
        current plan domainRegistry compositionRegistry None.
Proof.
  intros current plan domainRegistry compositionRegistry Havailable.
  destruct Havailable as [qualification Havailable].
  destruct Havailable as [Hpresent Hvalid].
  discriminate Hpresent.
Qed.

Theorem qualification_artifact_mismatch_cannot_qualify :
  forall current plan domainRegistry compositionRegistry qualification,
    qualificationArtifact qualification <> planArtifact plan ->
    ~ DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification.
Proof.
  intros current plan domainRegistry compositionRegistry qualification Hmismatch Hvalid.
  apply Hmismatch.
  exact (qualifiedExactArtifact
    current plan domainRegistry compositionRegistry qualification Hvalid).
Qed.

Theorem qualified_deployment_is_current_at_explicit_observation :
  forall current plan domainRegistry compositionRegistry qualification,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
    PointWithin current
      (qualificationValidFrom qualification)
      (qualificationValidUntil qualification).
Proof.
  intros current plan domainRegistry compositionRegistry qualification Hvalid.
  exact (qualifiedCurrent
    current plan domainRegistry compositionRegistry qualification Hvalid).
Qed.

Theorem stale_qualification_cannot_qualify :
  forall current plan domainRegistry compositionRegistry qualification,
    ~ PointWithin current
        (qualificationValidFrom qualification)
        (qualificationValidUntil qualification) ->
    ~ DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification.
Proof.
  intros current plan domainRegistry compositionRegistry qualification Hstale Hvalid.
  apply Hstale.
  exact (qualifiedCurrent
    current plan domainRegistry compositionRegistry qualification Hvalid).
Qed.

Theorem every_selected_domain_has_exact_evidence :
  forall current plan domainRegistry compositionRegistry qualification domain,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
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
        domainEvidenceClaim evidence claim = true).
Proof.
  intros current plan domainRegistry compositionRegistry qualification domain Hvalid Hdomain.
  exact (qualifiedEverySelectedDomainHasEvidence
    current plan domainRegistry compositionRegistry qualification Hvalid domain Hdomain).
Qed.

Theorem no_unselected_domain_can_gain_evidence_binding :
  forall current plan domainRegistry compositionRegistry qualification domain key,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
    qualificationDomainEvidence qualification domain = Some key ->
    planDomain plan domain = true.
Proof.
  intros current plan domainRegistry compositionRegistry qualification domain key Hvalid Hbinding.
  exact (qualifiedNoExtraDomainBinding
    current plan domainRegistry compositionRegistry qualification Hvalid domain key Hbinding).
Qed.

Theorem composite_deployment_has_explicit_composition_evidence :
  forall current plan domainRegistry compositionRegistry qualification,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
    planComposite plan = true ->
    exists key evidence,
      qualificationCompositionEvidence qualification = Some key /\
      compositionRegistry key = Some evidence /\
      compositionEvidenceArtifact evidence = planArtifact plan /\
      compositionEvidencePolicy evidence = planPolicy plan /\
      compositionEvidenceTopologyRevision evidence = planTopologyRevision plan /\
      PointWithin current
        (compositionEvidenceValidFrom evidence)
        (compositionEvidenceValidUntil evidence) /\
      IntervalWithin
        (qualificationValidFrom qualification)
        (qualificationValidUntil qualification)
        (compositionEvidenceValidFrom evidence)
        (compositionEvidenceValidUntil evidence) /\
      (forall domain,
        compositionEvidenceDomain evidence domain = planDomain plan domain) /\
      (forall link,
        compositionEvidenceLink evidence link = planLink plan link) /\
      (forall claim,
        compositionEvidenceClaim evidence claim = planClaim plan claim).
Proof.
  intros current plan domainRegistry compositionRegistry qualification Hvalid Hcomposite.
  pose proof
    (qualifiedCompositionEvidence
      current plan domainRegistry compositionRegistry qualification Hvalid)
    as Hcomposition.
  unfold CompositeEvidenceRequirement in Hcomposition.
  rewrite Hcomposite in Hcomposition.
  exact Hcomposition.
Qed.

Theorem independent_domain_attestations_cannot_replace_composition_evidence :
  forall current plan domainRegistry compositionRegistry qualification,
    planComposite plan = true ->
    qualificationCompositionEvidence qualification = None ->
    ~ DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification.
Proof.
  intros current plan domainRegistry compositionRegistry qualification Hcomposite Hmissing Hvalid.
  pose proof
    (composite_deployment_has_explicit_composition_evidence
      current plan domainRegistry compositionRegistry qualification Hvalid Hcomposite)
    as Hcomposition.
  destruct Hcomposition as [key Hcomposition].
  destruct Hcomposition as [evidence Hcomposition].
  destruct Hcomposition as [Hbinding Hrest].
  rewrite Hmissing in Hbinding.
  discriminate Hbinding.
Qed.

Theorem noncomposite_deployment_rejects_unexpected_composition_evidence :
  forall current plan domainRegistry compositionRegistry qualification key,
    planComposite plan = false ->
    qualificationCompositionEvidence qualification = Some key ->
    ~ DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification.
Proof.
  intros current plan domainRegistry compositionRegistry qualification key Hsimple Hunexpected Hvalid.
  pose proof
    (qualifiedCompositionEvidence
      current plan domainRegistry compositionRegistry qualification Hvalid)
    as Hcomposition.
  unfold CompositeEvidenceRequirement in Hcomposition.
  rewrite Hsimple in Hcomposition.
  rewrite Hunexpected in Hcomposition.
  discriminate Hcomposition.
Qed.
