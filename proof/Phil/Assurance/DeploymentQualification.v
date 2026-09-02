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

Definition DeploymentPlanWellFormed
  (plan : DeploymentPlanModel) : Prop :=
  planTopologyIdentityValid plan = true /\
  planLinksWellFormed plan = true /\
  (forall claim,
    planClaim plan claim = true ->
    exists domain,
      planDomain plan domain = true /\
      planClaimDomain plan claim domain = true) /\
  (forall claim domain,
    planClaimDomain plan claim domain = true ->
    planClaim plan claim = true /\
    planDomain plan domain = true).

Definition DeploymentQualificationMatchesPlan
  (plan : DeploymentPlanModel)
  (qualification : DeploymentQualificationModel) : Prop :=
  qualificationArtifact qualification = planArtifact plan /\
  qualificationPolicy qualification = planPolicy plan /\
  qualificationTopologyRevision qualification = planTopologyRevision plan /\
  (forall claim,
    qualificationClaim qualification claim = planClaim plan claim) /\
  qualificationIdentityValid qualification = true.

Definition DeploymentDomainEvidenceValid
  (current : DeploymentObservation)
  (plan : DeploymentPlanModel)
  (registry : DeploymentDomainEvidenceRegistry)
  (qualification : DeploymentQualificationModel) : Prop :=
  (forall domain,
    planDomain plan domain = true ->
    exists key evidence,
      qualificationDomainEvidence qualification domain = Some key /\
      registry key = Some evidence /\
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
        domainEvidenceClaim evidence claim = true)) /\
  (forall domain key,
    qualificationDomainEvidence qualification domain = Some key ->
    planDomain plan domain = true).

Definition DeploymentCompositionEvidenceValid
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

Definition DeploymentQualificationValid
  (current : DeploymentObservation)
  (plan : DeploymentPlanModel)
  (domainRegistry : DeploymentDomainEvidenceRegistry)
  (compositionRegistry : DeploymentCompositionEvidenceRegistry)
  (qualification : DeploymentQualificationModel) : Prop :=
  DeploymentPlanWellFormed plan /\
  DeploymentQualificationMatchesPlan plan qualification /\
  PointWithin current
    (qualificationValidFrom qualification)
    (qualificationValidUntil qualification) /\
  DeploymentDomainEvidenceValid current plan domainRegistry qualification /\
  DeploymentCompositionEvidenceValid current plan compositionRegistry qualification.

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
  destruct Hvalid as [_ [Hmatches _]].
  exact Hmatches.
Qed.

Theorem raw_attestation_without_qualification_cannot_close :
  forall current plan domainRegistry compositionRegistry,
    ~ DeploymentQualificationAvailable
        current plan domainRegistry compositionRegistry None.
Proof.
  intros current plan domainRegistry compositionRegistry Havailable.
  destruct Havailable as [qualification [Hpresent _]].
  discriminate Hpresent.
Qed.

Theorem qualification_artifact_mismatch_cannot_qualify :
  forall current plan domainRegistry compositionRegistry qualification,
    qualificationArtifact qualification <> planArtifact plan ->
    ~ DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification.
Proof.
  intros current plan domainRegistry compositionRegistry qualification Hmismatch Hvalid.
  pose proof
    (qualified_deployment_uses_exact_plan_identity
      current plan domainRegistry compositionRegistry qualification Hvalid)
    as Hidentity.
  destruct Hidentity as [Hartifact _].
  exact (Hmismatch Hartifact).
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
  destruct Hvalid as [_ [_ [Hcurrent _]]].
  exact Hcurrent.
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
  exact (qualified_deployment_is_current_at_explicit_observation
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
  destruct Hvalid as [_ [_ [_ [Hdomains _]]]].
  destruct Hdomains as [Htotal _].
  exact (Htotal domain Hdomain).
Qed.

Theorem no_unselected_domain_can_gain_evidence_binding :
  forall current plan domainRegistry compositionRegistry qualification domain key,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
    qualificationDomainEvidence qualification domain = Some key ->
    planDomain plan domain = true.
Proof.
  intros current plan domainRegistry compositionRegistry qualification domain key Hvalid Hbinding.
  destruct Hvalid as [_ [_ [_ [Hdomains _]]]].
  destruct Hdomains as [_ Hnoextra].
  exact (Hnoextra domain key Hbinding).
Qed.

Theorem selected_domain_evidence_is_current :
  forall current plan domainRegistry compositionRegistry qualification domain,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
    planDomain plan domain = true ->
    exists key evidence,
      qualificationDomainEvidence qualification domain = Some key /\
      domainRegistry key = Some evidence /\
      PointWithin current
        (domainEvidenceValidFrom evidence)
        (domainEvidenceValidUntil evidence).
Proof.
  intros current plan domainRegistry compositionRegistry qualification domain Hvalid Hdomain.
  destruct (every_selected_domain_has_exact_evidence
    current plan domainRegistry compositionRegistry qualification domain Hvalid Hdomain)
    as [key [evidence [Hbinding [Hregistry [_ [_ [_ [Hcurrent _]]]]]]]]].
  exists key, evidence.
  repeat split; assumption.
Qed.

Theorem qualification_never_outlives_selected_domain_evidence :
  forall current plan domainRegistry compositionRegistry qualification domain,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
    planDomain plan domain = true ->
    exists key evidence,
      qualificationDomainEvidence qualification domain = Some key /\
      domainRegistry key = Some evidence /\
      IntervalWithin
        (qualificationValidFrom qualification)
        (qualificationValidUntil qualification)
        (domainEvidenceValidFrom evidence)
        (domainEvidenceValidUntil evidence).
Proof.
  intros current plan domainRegistry compositionRegistry qualification domain Hvalid Hdomain.
  destruct (every_selected_domain_has_exact_evidence
    current plan domainRegistry compositionRegistry qualification domain Hvalid Hdomain)
    as [key [evidence [Hbinding [Hregistry [_ [_ [_ [_ [Hinterval _]]]]]]]]].
  exists key, evidence.
  repeat split; assumption.
Qed.

Theorem domain_evidence_covers_every_assigned_claim :
  forall current plan domainRegistry compositionRegistry qualification domain claim,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
    planDomain plan domain = true ->
    planClaimDomain plan claim domain = true ->
    exists key evidence,
      qualificationDomainEvidence qualification domain = Some key /\
      domainRegistry key = Some evidence /\
      domainEvidenceClaim evidence claim = true.
Proof.
  intros current plan domainRegistry compositionRegistry qualification domain claim
    Hvalid Hdomain Hassigned.
  destruct (every_selected_domain_has_exact_evidence
    current plan domainRegistry compositionRegistry qualification domain Hvalid Hdomain)
    as [key [evidence [Hbinding [Hregistry [_ [_ [_ [_ [_ Hclaims]]]]]]]]].
  exists key, evidence.
  repeat split; try assumption.
  exact (Hclaims claim Hassigned).
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
  destruct Hvalid as [_ [_ [_ [_ Hcomposition]]]].
  unfold DeploymentCompositionEvidenceValid in Hcomposition.
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
  destruct (composite_deployment_has_explicit_composition_evidence
    current plan domainRegistry compositionRegistry qualification Hvalid Hcomposite)
    as [key [evidence [Hbinding _]]].
  rewrite Hmissing in Hbinding.
  discriminate.
Qed.

Theorem composition_evidence_matches_complete_topology :
  forall current plan domainRegistry compositionRegistry qualification,
    DeploymentQualificationValid
      current plan domainRegistry compositionRegistry qualification ->
    planComposite plan = true ->
    exists key evidence,
      qualificationCompositionEvidence qualification = Some key /\
      compositionRegistry key = Some evidence /\
      (forall domain,
        compositionEvidenceDomain evidence domain = planDomain plan domain) /\
      (forall link,
        compositionEvidenceLink evidence link = planLink plan link) /\
      (forall claim,
        compositionEvidenceClaim evidence claim = planClaim plan claim).
Proof.
  intros current plan domainRegistry compositionRegistry qualification Hvalid Hcomposite.
  destruct (composite_deployment_has_explicit_composition_evidence
    current plan domainRegistry compositionRegistry qualification Hvalid Hcomposite)
    as [key [evidence
      [Hbinding [Hregistry [_ [_ [_ [_ [_ [Hdomains [Hlinks Hclaims]]]]]]]]]]].
  exists key, evidence.
  repeat split; assumption.
Qed.

Theorem noncomposite_deployment_rejects_unexpected_composition_evidence :
  forall current plan domainRegistry compositionRegistry qualification key,
    planComposite plan = false ->
    qualificationCompositionEvidence qualification = Some key ->
    ~ DeploymentQualificationValid
        current plan domainRegistry compositionRegistry qualification.
Proof.
  intros current plan domainRegistry compositionRegistry qualification key Hsimple Hunexpected Hvalid.
  destruct Hvalid as [_ [_ [_ [_ Hcomposition]]]].
  unfold DeploymentCompositionEvidenceValid in Hcomposition.
  rewrite Hsimple in Hcomposition.
  rewrite Hunexpected in Hcomposition.
  discriminate.
Qed.
