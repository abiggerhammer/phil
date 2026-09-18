From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ProviderQualification AuthorityPossession.

(*
  PHIL-EXEC-AMBIENT-001 — explicit environmental observation and bounded
  nondeterminism.

  Ordinary computation has no ambient environment authority.  An observation
  is admitted only through an explicit identity-bearing relation whose
  provenance is already competent.  Provider and capability provenance compose
  the Certified PHIL-PROV-QUAL-001 and PHIL-AUTH-POSSESS-001 authorities rather
  than re-defining them here.
*)

Definition ObservationKind := nat.
Definition ObservationRelationKey := nat.

Inductive ObservationProvenance : Type :=
| EntryProvenance (identity : nat)
| ProviderProvenance
    (contract : ProviderContract)
    (implementation : ProviderImplementation)
    (claim : ProviderQualificationClaim)
    (operation : ProviderOperationKey)
    (operationContract : ProviderOperationContract)
| CapabilityProvenance
    (requirement : AuthorityRequirement)
    (capability : AuthorityCapability)
| ProtocolProvenance (identity : nat)
| BoundaryProvenance (identity : nat)
| AssumptionProvenance (identity : nat)
| DeploymentProvenance (identity : nat).

Record ObservationRelation : Type := mkObservationRelation {
  observationRelationKey : ObservationRelationKey;
  observationRelationKind : ObservationKind;
  observationRelationProvenance : ObservationProvenance
}.

Definition provenanceAdmissible
  (provenance : ObservationProvenance) : Prop :=
  match provenance with
  | EntryProvenance _ => True
  | ProviderProvenance contract implementation claim operation operationContract =>
      ProviderQualifies contract implementation claim /\
      providerOperations contract operation = Some operationContract
  | CapabilityProvenance requirement capability =>
      authorityExerciseAllowed requirement PossessedCapability capability = true
  | ProtocolProvenance _ => True
  | BoundaryProvenance _ => True
  | AssumptionProvenance _ => True
  | DeploymentProvenance _ => True
  end.

Inductive EnvironmentObservationSource : Type :=
| ExplicitObservation (relation : ObservationRelation)
| AmbientObservation (kind : ObservationKind)
| RuntimeObservationHandle
| BackendObservationSymbol
| AmbientObservationRegistryEntry.

Definition ObservationAccepted
  (requested : ObservationKind)
  (source : EnvironmentObservationSource) : Prop :=
  match source with
  | ExplicitObservation relation =>
      observationRelationKind relation = requested /\
      provenanceAdmissible (observationRelationProvenance relation)
  | _ => False
  end.

Theorem ambient_observation_never_authorizes :
  forall requested ambientKind,
    ~ ObservationAccepted requested (AmbientObservation ambientKind).
Proof.
  intros requested ambientKind H.
  exact H.
Qed.

Theorem runtime_handle_never_authorizes_environment_observation :
  forall requested,
    ~ ObservationAccepted requested RuntimeObservationHandle.
Proof.
  intros requested H.
  exact H.
Qed.

Theorem backend_symbol_never_authorizes_environment_observation :
  forall requested,
    ~ ObservationAccepted requested BackendObservationSymbol.
Proof.
  intros requested H.
  exact H.
Qed.

Theorem ambient_registry_entry_never_authorizes_environment_observation :
  forall requested,
    ~ ObservationAccepted requested AmbientObservationRegistryEntry.
Proof.
  intros requested H.
  exact H.
Qed.

Theorem explicit_relation_cannot_be_relabelled :
  forall requested relation,
    requested <> observationRelationKind relation ->
    ~ ObservationAccepted requested (ExplicitObservation relation).
Proof.
  intros requested relation Hneq Haccepted.
  destruct Haccepted as [Hkind _].
  apply Hneq.
  symmetry.
  exact Hkind.
Qed.

Theorem explicit_entry_relation_accepts_exact_kind :
  forall key kind identity,
    ObservationAccepted kind
      (ExplicitObservation
        (mkObservationRelation key kind (EntryProvenance identity))).
Proof.
  intros.
  split.
  - reflexivity.
  - exact I.
Qed.

Theorem explicit_protocol_relation_accepts_exact_kind :
  forall key kind identity,
    ObservationAccepted kind
      (ExplicitObservation
        (mkObservationRelation key kind (ProtocolProvenance identity))).
Proof.
  intros.
  split.
  - reflexivity.
  - exact I.
Qed.

Theorem explicit_boundary_relation_accepts_exact_kind :
  forall key kind identity,
    ObservationAccepted kind
      (ExplicitObservation
        (mkObservationRelation key kind (BoundaryProvenance identity))).
Proof.
  intros.
  split.
  - reflexivity.
  - exact I.
Qed.

Theorem explicit_assumption_relation_accepts_exact_kind :
  forall key kind identity,
    ObservationAccepted kind
      (ExplicitObservation
        (mkObservationRelation key kind (AssumptionProvenance identity))).
Proof.
  intros.
  split.
  - reflexivity.
  - exact I.
Qed.

Theorem explicit_deployment_relation_accepts_exact_kind :
  forall key kind identity,
    ObservationAccepted kind
      (ExplicitObservation
        (mkObservationRelation key kind (DeploymentProvenance identity))).
Proof.
  intros.
  split.
  - reflexivity.
  - exact I.
Qed.

Theorem qualified_provider_relation_accepts_exact_kind :
  forall key kind contract implementation claim operation operationContract,
    ProviderQualifies contract implementation claim ->
    providerOperations contract operation = Some operationContract ->
    ObservationAccepted kind
      (ExplicitObservation
        (mkObservationRelation key kind
          (ProviderProvenance
            contract implementation claim operation operationContract))).
Proof.
  intros key kind contract implementation claim operation operationContract
    Hqualified Hoperation.
  split.
  - reflexivity.
  - simpl.
    split.
    + exact Hqualified.
    + exact Hoperation.
Qed.

Theorem accepted_provider_observation_has_explicit_operation_correspondence :
  forall key kind contract implementation claim operation operationContract,
    ObservationAccepted kind
      (ExplicitObservation
        (mkObservationRelation key kind
          (ProviderProvenance
            contract implementation claim operation operationContract))) ->
    exists correspondence implementationOperation,
      claimCorrespondences claim operation = Some correspondence /\
      providerEntries implementation (correspondenceEntry correspondence) =
        Some implementationOperation /\
      ProviderOperationQualifies
        operationContract implementationOperation correspondence.
Proof.
  intros key kind contract implementation claim operation operationContract
    Haccepted.
  destruct Haccepted as [_ Hprovenance].
  simpl in Hprovenance.
  destruct Hprovenance as [Hqualified Hoperation].
  eapply every_public_operation_has_explicit_correspondence.
  - exact Hqualified.
  - exact Hoperation.
Qed.

Theorem qualified_provider_nondeterminism_is_bounded_by_contract_outcomes :
  forall operationContract implementationOperation correspondence
    implementationOutcome implementationResidue,
    ProviderOperationQualifies
      operationContract implementationOperation correspondence ->
    implementationOutcomeResidues implementationOperation implementationOutcome =
      Some implementationResidue ->
    exists contractOutcome contractResidue,
      correspondenceOutcomes correspondence implementationOutcome =
        Some contractOutcome /\
      contractOutcomeResidues operationContract contractOutcome =
        Some contractResidue /\
      implementationResidue = contractResidue.
Proof.
  intros operationContract implementationOperation correspondence
    implementationOutcome implementationResidue Hqualified Hresidue.
  eapply every_implementation_outcome_is_explicitly_mapped.
  - exact Hqualified.
  - exact Hresidue.
Qed.

Theorem checked_capability_relation_accepts_exact_kind :
  forall key kind requirement capability,
    authorityExerciseAllowed requirement PossessedCapability capability = true ->
    ObservationAccepted kind
      (ExplicitObservation
        (mkObservationRelation key kind
          (CapabilityProvenance requirement capability))).
Proof.
  intros key kind requirement capability Hallowed.
  split.
  - reflexivity.
  - simpl.
    exact Hallowed.
Qed.

Theorem runtime_authority_handle_cannot_substitute_for_capability_provenance :
  forall requirement capability,
    authorityExerciseAllowed
      requirement RuntimeAuthorityHandle capability = false.
Proof.
  apply runtime_handle_is_not_possession.
Qed.

Theorem backend_authority_symbol_cannot_substitute_for_capability_provenance :
  forall requirement capability,
    authorityExerciseAllowed
      requirement BackendAuthoritySymbol capability = false.
Proof.
  apply backend_symbol_is_not_possession.
Qed.

Theorem ambient_authority_registry_cannot_substitute_for_capability_provenance :
  forall requirement capability,
    authorityExerciseAllowed
      requirement AmbientAuthorityRegistryEntry capability = false.
Proof.
  apply ambient_registry_entry_is_not_possession.
Qed.
