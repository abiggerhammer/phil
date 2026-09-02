From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import StorageRealization.

(*
  PHIL-MEM-FAIL-001 — no undeclared allocation-failure widening.

  This normalized model extends the already-Certified PHIL-MEM-REALIZE-001
  storage realization relation with only the source-visible failure surface and
  the physical allocation-failure disposition used by Phil.Systems.Storage.

  The theorem family is deliberately bounded to MEM-002/MEM-003.  General
  target-independent runtime partiality remains a separate obligation.  Truth
  of capacity evidence, assumptions, deployment facts, and concrete allocator
  behavior remain explicit evidence/profile boundaries.
*)

Definition StorageFailureKey := nat.
Definition StorageCapacityEvidenceKey := nat.
Definition StorageAssumptionKey := nat.
Definition StorageDeploymentRequirementKey := nat.

Inductive SourceStorageFailureSurface : Type :=
| SourceStorageInfallible
| SourceStorageFailures :
    (StorageFailureKey -> bool) -> SourceStorageFailureSurface.

Inductive StorageFailureDisposition : Type :=
| StorageFailureMapsToSource :
    StorageFailureKey -> StorageFailureDisposition
| StorageFailureProvedUnreachable :
    StorageCapacityEvidenceKey -> StorageFailureDisposition
| StorageFailureAssumption :
    StorageAssumptionKey -> StorageFailureDisposition
| StorageFailureDeploymentRequirement :
    StorageDeploymentRequirementKey -> StorageFailureDisposition
| StorageFailureUnaccounted.

Inductive PhysicalAllocationFailure : Type :=
| PhysicalAllocationCannotFail
| PhysicalAllocationMayFail :
    StorageFailureDisposition -> PhysicalAllocationFailure.

Definition sourceFailureContains
  (failure : StorageFailureKey)
  (surface : SourceStorageFailureSurface) : bool :=
  match surface with
  | SourceStorageInfallible => false
  | SourceStorageFailures failures => failures failure
  end.

Definition StorageFailureDispositionValid
  (surface : SourceStorageFailureSurface)
  (physicalFailure : PhysicalAllocationFailure) : Prop :=
  match physicalFailure with
  | PhysicalAllocationCannotFail => True
  | PhysicalAllocationMayFail disposition =>
      match disposition with
      | StorageFailureMapsToSource failure =>
          failure <> 0 /\ sourceFailureContains failure surface = true
      | StorageFailureProvedUnreachable evidence => evidence <> 0
      | StorageFailureAssumption assumption => assumption <> 0
      | StorageFailureDeploymentRequirement requirement => requirement <> 0
      | StorageFailureUnaccounted => False
      end
  end.

Record StorageFailureRealizationFacts : Type := mkStorageFailureRealizationFacts {
  storageFailureBase : StorageRealizationFacts;
  storageFailureSourceSurface : SourceStorageFailureSurface;
  storageFailurePhysicalFailure : PhysicalAllocationFailure
}.

Definition StorageFailureRealizationValid
  (facts : StorageFailureRealizationFacts) : Prop :=
  StorageRealizationValid (storageFailureBase facts) /\
  StorageFailureDispositionValid
    (storageFailureSourceSurface facts)
    (storageFailurePhysicalFailure facts).

Definition makeStorageFailureRealization
  (base : StorageRealizationFacts)
  (surface : SourceStorageFailureSurface)
  (physicalFailure : PhysicalAllocationFailure) : StorageFailureRealizationFacts :=
  mkStorageFailureRealizationFacts base surface physicalFailure.

Definition storage_failure_semantic_identity
  (facts : StorageFailureRealizationFacts) : option StorageSemanticIdentity :=
  storage_semantic_identity (storageFailureBase facts).

Theorem accepted_failure_realization_preserves_base_validity :
  forall facts,
    StorageFailureRealizationValid facts ->
    StorageRealizationValid (storageFailureBase facts).
Proof.
  intros facts Hvalid.
  unfold StorageFailureRealizationValid in Hvalid.
  destruct Hvalid as [Hbase _].
  exact Hbase.
Qed.

Theorem allocation_cannot_fail_preserves_storage_realization :
  forall base surface,
    StorageRealizationValid base ->
    StorageFailureRealizationValid
      (makeStorageFailureRealization
        base surface PhysicalAllocationCannotFail).
Proof.
  intros base surface Hbase.
  unfold StorageFailureRealizationValid, makeStorageFailureRealization.
  simpl.
  split.
  - exact Hbase.
  - exact I.
Qed.

Theorem unaccounted_allocation_failure_cannot_be_certified :
  forall base surface,
    ~ StorageFailureRealizationValid
        (makeStorageFailureRealization
          base surface
          (PhysicalAllocationMayFail StorageFailureUnaccounted)).
Proof.
  intros base surface Hvalid.
  unfold StorageFailureRealizationValid, makeStorageFailureRealization,
    StorageFailureDispositionValid in Hvalid.
  simpl in Hvalid.
  destruct Hvalid as [_ Hfalse].
  exact Hfalse.
Qed.

Theorem mapped_failure_requires_declared_source_outcome :
  forall base surface failure,
    StorageFailureRealizationValid
      (makeStorageFailureRealization
        base surface
        (PhysicalAllocationMayFail (StorageFailureMapsToSource failure))) ->
    failure <> 0 /\ sourceFailureContains failure surface = true.
Proof.
  intros base surface failure Hvalid.
  unfold StorageFailureRealizationValid, makeStorageFailureRealization,
    StorageFailureDispositionValid in Hvalid.
  simpl in Hvalid.
  exact (proj2 Hvalid).
Qed.

Theorem infallible_source_rejects_mapped_allocation_failure :
  forall base failure,
    ~ StorageFailureRealizationValid
        (makeStorageFailureRealization
          base SourceStorageInfallible
          (PhysicalAllocationMayFail (StorageFailureMapsToSource failure))).
Proof.
  intros base failure Hvalid.
  pose proof
    (mapped_failure_requires_declared_source_outcome
      base SourceStorageInfallible failure Hvalid)
    as Hmapped.
  destruct Hmapped as [_ Hcontains].
  simpl in Hcontains.
  discriminate Hcontains.
Qed.

Theorem exact_declared_source_failure_mapping_accepts :
  forall base failures failure,
    StorageRealizationValid base ->
    failure <> 0 ->
    failures failure = true ->
    StorageFailureRealizationValid
      (makeStorageFailureRealization
        base
        (SourceStorageFailures failures)
        (PhysicalAllocationMayFail (StorageFailureMapsToSource failure))).
Proof.
  intros base failures failure Hbase Hfailure Hdeclared.
  unfold StorageFailureRealizationValid, makeStorageFailureRealization,
    StorageFailureDispositionValid.
  simpl.
  split.
  - exact Hbase.
  - split; assumption.
Qed.

Theorem accepted_capacity_evidence_is_explicit :
  forall base surface evidence,
    StorageFailureRealizationValid
      (makeStorageFailureRealization
        base surface
        (PhysicalAllocationMayFail
          (StorageFailureProvedUnreachable evidence))) ->
    evidence <> 0.
Proof.
  intros base surface evidence Hvalid.
  unfold StorageFailureRealizationValid, makeStorageFailureRealization,
    StorageFailureDispositionValid in Hvalid.
  simpl in Hvalid.
  exact (proj2 Hvalid).
Qed.

Theorem accepted_allocation_assumption_is_explicit :
  forall base surface assumption,
    StorageFailureRealizationValid
      (makeStorageFailureRealization
        base surface
        (PhysicalAllocationMayFail
          (StorageFailureAssumption assumption))) ->
    assumption <> 0.
Proof.
  intros base surface assumption Hvalid.
  unfold StorageFailureRealizationValid, makeStorageFailureRealization,
    StorageFailureDispositionValid in Hvalid.
  simpl in Hvalid.
  exact (proj2 Hvalid).
Qed.

Theorem accepted_deployment_requirement_is_explicit :
  forall base surface requirement,
    StorageFailureRealizationValid
      (makeStorageFailureRealization
        base surface
        (PhysicalAllocationMayFail
          (StorageFailureDeploymentRequirement requirement))) ->
    requirement <> 0.
Proof.
  intros base surface requirement Hvalid.
  unfold StorageFailureRealizationValid, makeStorageFailureRealization,
    StorageFailureDispositionValid in Hvalid.
  simpl in Hvalid.
  exact (proj2 Hvalid).
Qed.

Theorem accepted_potential_failure_has_one_explicit_disposition :
  forall base surface disposition,
    StorageFailureRealizationValid
      (makeStorageFailureRealization
        base surface (PhysicalAllocationMayFail disposition)) ->
    (exists failure,
      disposition = StorageFailureMapsToSource failure /\
      failure <> 0 /\
      sourceFailureContains failure surface = true) \/
    (exists evidence,
      disposition = StorageFailureProvedUnreachable evidence /\
      evidence <> 0) \/
    (exists assumption,
      disposition = StorageFailureAssumption assumption /\
      assumption <> 0) \/
    (exists requirement,
      disposition = StorageFailureDeploymentRequirement requirement /\
      requirement <> 0).
Proof.
  intros base surface disposition Hvalid.
  unfold StorageFailureRealizationValid, makeStorageFailureRealization,
    StorageFailureDispositionValid in Hvalid.
  simpl in Hvalid.
  destruct Hvalid as [_ Hdisposition].
  destruct disposition as [failure | evidence | assumption | requirement |].
  - left.
    exists failure.
    split.
    + reflexivity.
    + exact Hdisposition.
  - right; left.
    exists evidence.
    split.
    + reflexivity.
    + exact Hdisposition.
  - right; right; left.
    exists assumption.
    split.
    + reflexivity.
    + exact Hdisposition.
  - right; right; right.
    exists requirement.
    split.
    + reflexivity.
    + exact Hdisposition.
  - contradiction.
Qed.

Theorem allocation_failure_disposition_does_not_rewrite_semantic_identity :
  forall base surface firstFailure secondFailure,
    storage_failure_semantic_identity
      (makeStorageFailureRealization base surface firstFailure) =
    storage_failure_semantic_identity
      (makeStorageFailureRealization base surface secondFailure).
Proof.
  reflexivity.
Qed.
