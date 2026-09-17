From Stdlib Require Import Lists.List.

Import ListNotations.

From Phil.Core Require Import GenericInstantiation.

(*
  PHIL-ASSURE-GENERIC-001 — reusable conditional assurance for generic bodies.

  The generic body is checked once against one exact declaration/interface/
  definition/public-requirement identity.  Ordinary applications reuse that
  body assurance only through their own already-checked generic-discharge
  lineage.  This layer does not re-prove evidence truth, provider refinement,
  or assurance-policy authority; those remain predecessor competence boundaries.
*)

Definition DeclarationIdentity : Type := nat.
Definition InterfaceIdentity : Type := nat.
Definition DefinitionIdentity : Type := nat.
Definition RequirementRevision : Type := nat.
Definition EvidenceArtifactIdentity : Type := nat.
Definition ApplicationIdentity : Type := nat.
Definition RealizationIdentity : Type := nat.

Record ReusableGenericBodyAssurance : Type := mkReusableGenericBodyAssurance {
  genericBodyDeclaration : DeclarationIdentity;
  genericBodyInterface : InterfaceIdentity;
  genericBodyDefinition : DefinitionIdentity;
  genericBodyRequirements : list GenericRequirement;
  genericBodyRequirementRevisions : list RequirementRevision;
  genericBodyEvidenceArtifact : EvidenceArtifactIdentity
}.

Record GenericApplicationLineage : Type := mkGenericApplicationLineage {
  genericApplicationIdentity : ApplicationIdentity;
  genericApplicationDeclaration : DeclarationIdentity;
  genericApplicationInterface : InterfaceIdentity;
  genericApplicationDefinition : DefinitionIdentity;
  genericApplicationDispositions :
    list (GenericRequirement * GenericRequirementDisposition)
}.

Record GenericApplicationAssurance : Type := mkGenericApplicationAssurance {
  genericApplicationAssuranceBody : ReusableGenericBodyAssurance;
  genericApplicationAssuranceLineage : GenericApplicationLineage
}.

Definition CheckedGenericApplicationAssurance
  (policy : GenericInstantiationPolicy)
  (body : ReusableGenericBodyAssurance)
  (currentRequirements : list GenericRequirement)
  (currentRequirementRevisions : list RequirementRevision)
  (lineage : GenericApplicationLineage)
  (assurance : GenericApplicationAssurance) : Prop :=
  genericApplicationAssuranceBody assurance = body /\
  genericApplicationAssuranceLineage assurance = lineage /\
  genericApplicationDeclaration lineage = genericBodyDeclaration body /\
  genericApplicationInterface lineage = genericBodyInterface body /\
  genericApplicationDefinition lineage = genericBodyDefinition body /\
  currentRequirements = genericBodyRequirements body /\
  currentRequirementRevisions = genericBodyRequirementRevisions body /\
  acceptedInstantiation
    policy currentRequirements (genericApplicationDispositions lineage).

Theorem checked_generic_application_retains_exact_reusable_body :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance,
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage assurance ->
    genericApplicationAssuranceBody assurance = body.
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance Hchecked.
  destruct Hchecked as [Hbody _].
  exact Hbody.
Qed.

Theorem checked_generic_application_retains_exact_discharge_lineage :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance,
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage assurance ->
    genericApplicationAssuranceLineage assurance = lineage.
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance Hchecked.
  destruct Hchecked as [_ [Hlineage _]].
  exact Hlineage.
Qed.

Theorem checked_generic_application_requires_exact_body_identity :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance,
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage assurance ->
    genericApplicationDeclaration lineage = genericBodyDeclaration body /\
    genericApplicationInterface lineage = genericBodyInterface body /\
    genericApplicationDefinition lineage = genericBodyDefinition body.
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance Hchecked.
  destruct Hchecked as
    [_ [_ [Hdeclaration [Hinterface [Hdefinition _]]]]].
  repeat split; assumption.
Qed.

Theorem checked_generic_application_requires_exact_public_requirements :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance,
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage assurance ->
    currentRequirements = genericBodyRequirements body /\
    currentRequirementRevisions = genericBodyRequirementRevisions body.
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance Hchecked.
  destruct Hchecked as
    [_ [_ [_ [_ [_ [Hrequirements [Hrevisions _]]]]]]].
  split; assumption.
Qed.

Theorem checked_generic_application_has_disposition_for_every_public_requirement :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance requirement,
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage assurance ->
    In requirement (genericBodyRequirements body) ->
    exists disposition,
      In (requirement, disposition) (genericApplicationDispositions lineage).
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance requirement
    Hchecked Hin.
  destruct Hchecked as
    [_ [_ [_ [_ [_ [Hrequirements [_ Haccepted]]]]]]].
  rewrite <- Hrequirements in Hin.
  eapply accepted_instantiation_has_disposition_for_every_requirement.
  - exact Haccepted.
  - exact Hin.
Qed.

Theorem checked_generic_application_has_no_unexposed_disposition :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance
    requirement disposition,
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage assurance ->
    In (requirement, disposition) (genericApplicationDispositions lineage) ->
    In requirement (genericBodyRequirements body).
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance
    requirement disposition Hchecked Hin.
  destruct Hchecked as
    [_ [_ [_ [_ [_ [Hrequirements [_ Haccepted]]]]]]].
  pose proof
    (accepted_instantiation_has_no_unexposed_disposition
      policy currentRequirements (genericApplicationDispositions lineage)
      requirement disposition Haccepted Hin) as Hcurrent.
  rewrite Hrequirements in Hcurrent.
  exact Hcurrent.
Qed.

Theorem strict_checked_generic_application_contains_no_assumptions :
  forall body currentRequirements currentRequirementRevisions lineage assurance requirement,
    CheckedGenericApplicationAssurance
      strictInstantiationPolicy body currentRequirements
      currentRequirementRevisions lineage assurance ->
    In (requirement, AssumptionDependent)
      (genericApplicationDispositions lineage) ->
    False.
Proof.
  intros body currentRequirements currentRequirementRevisions lineage assurance requirement
    Hchecked Hin.
  destruct Hchecked as
    [_ [_ [_ [_ [_ [_ [_ Haccepted]]]]]]].
  eapply strict_accepted_instantiation_contains_no_assumptions.
  - exact Haccepted.
  - exact Hin.
Qed.

Theorem strict_checked_generic_application_contains_no_exports :
  forall body currentRequirements currentRequirementRevisions lineage assurance requirement,
    CheckedGenericApplicationAssurance
      strictInstantiationPolicy body currentRequirements
      currentRequirementRevisions lineage assurance ->
    In (requirement, Exported)
      (genericApplicationDispositions lineage) ->
    False.
Proof.
  intros body currentRequirements currentRequirementRevisions lineage assurance requirement
    Hchecked Hin.
  destruct Hchecked as
    [_ [_ [_ [_ [_ [_ [_ Haccepted]]]]]]].
  eapply strict_accepted_instantiation_contains_no_exports.
  - exact Haccepted.
  - exact Hin.
Qed.

Theorem declaration_mismatch_cannot_reuse_body_assurance :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance,
    genericApplicationDeclaration lineage <> genericBodyDeclaration body ->
    ~ CheckedGenericApplicationAssurance
        policy body currentRequirements currentRequirementRevisions lineage assurance.
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance
    Hmismatch Hchecked.
  destruct Hchecked as [_ [_ [Hexact _]]].
  contradiction.
Qed.

Theorem interface_mismatch_cannot_reuse_body_assurance :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance,
    genericApplicationInterface lineage <> genericBodyInterface body ->
    ~ CheckedGenericApplicationAssurance
        policy body currentRequirements currentRequirementRevisions lineage assurance.
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance
    Hmismatch Hchecked.
  destruct Hchecked as [_ [_ [_ [Hexact _]]]].
  contradiction.
Qed.

Theorem definition_mismatch_cannot_reuse_body_assurance :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance,
    genericApplicationDefinition lineage <> genericBodyDefinition body ->
    ~ CheckedGenericApplicationAssurance
        policy body currentRequirements currentRequirementRevisions lineage assurance.
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance
    Hmismatch Hchecked.
  destruct Hchecked as [_ [_ [_ [_ [Hexact _]]]]].
  contradiction.
Qed.

Theorem public_requirement_revision_mismatch_cannot_reuse_body_assurance :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance,
    currentRequirementRevisions <> genericBodyRequirementRevisions body ->
    ~ CheckedGenericApplicationAssurance
        policy body currentRequirements currentRequirementRevisions lineage assurance.
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance
    Hmismatch Hchecked.
  destruct Hchecked as [_ [_ [_ [_ [_ [_ [Hexact _]]]]]]].
  contradiction.
Qed.

Theorem two_checked_applications_share_the_exact_body_assurance :
  forall policy body currentRequirements currentRequirementRevisions
    lineageA lineageB assuranceA assuranceB,
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineageA assuranceA ->
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineageB assuranceB ->
    genericApplicationAssuranceBody assuranceA =
      genericApplicationAssuranceBody assuranceB.
Proof.
  intros policy body currentRequirements currentRequirementRevisions
    lineageA lineageB assuranceA assuranceB HA HB.
  pose proof
    (checked_generic_application_retains_exact_reusable_body
      policy body currentRequirements currentRequirementRevisions lineageA assuranceA HA)
    as HbodyA.
  pose proof
    (checked_generic_application_retains_exact_reusable_body
      policy body currentRequirements currentRequirementRevisions lineageB assuranceB HB)
    as HbodyB.
  rewrite HbodyA, HbodyB.
  reflexivity.
Qed.

Definition replaceGenericApplicationIdentity
  (lineage : GenericApplicationLineage)
  (identity : ApplicationIdentity) : GenericApplicationLineage :=
  mkGenericApplicationLineage
    identity
    (genericApplicationDeclaration lineage)
    (genericApplicationInterface lineage)
    (genericApplicationDefinition lineage)
    (genericApplicationDispositions lineage).

Theorem application_identity_does_not_rekey_reusable_body_assurance :
  forall policy body currentRequirements currentRequirementRevisions lineage assurance newIdentity,
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions lineage assurance ->
    CheckedGenericApplicationAssurance
      policy body currentRequirements currentRequirementRevisions
      (replaceGenericApplicationIdentity lineage newIdentity)
      (mkGenericApplicationAssurance
        body (replaceGenericApplicationIdentity lineage newIdentity)).
Proof.
  intros policy body currentRequirements currentRequirementRevisions lineage assurance newIdentity
    Hchecked.
  destruct Hchecked as
    [_ [_ [Hdeclaration [Hinterface [Hdefinition
      [Hrequirements [Hrevisions Haccepted]]]]]]].
  unfold CheckedGenericApplicationAssurance, replaceGenericApplicationIdentity.
  simpl.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [exact Hdeclaration |].
  split; [exact Hinterface |].
  split; [exact Hdefinition |].
  split; [exact Hrequirements |].
  split; [exact Hrevisions |].
  exact Haccepted.
Qed.

Definition reusableBodyUnderRealization
  (body : ReusableGenericBodyAssurance)
  (_ : RealizationIdentity) : ReusableGenericBodyAssurance := body.

Theorem backend_realization_does_not_rekey_source_body_assurance :
  forall body firstRealization secondRealization,
    reusableBodyUnderRealization body firstRealization =
    reusableBodyUnderRealization body secondRealization.
Proof.
  reflexivity.
Qed.
