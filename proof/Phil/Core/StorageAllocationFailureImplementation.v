From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import StorageAllocationFailure.

(*
  Machine-facing decision surface for PHIL-MEM-FAIL-001.

  The already implementation-refined PHIL-MEM-REALIZE-001 predecessor is kept
  as one Boolean fact.  The remaining gates mirror the exact Certified
  StorageFailureDispositionValid case split without importing concrete Haskell
  Text/Set representation into the proof model.
*)

Definition decideStorageFailureRealizationByFacts
  (baseRealizationValid dispositionValid : bool) : bool :=
  andb baseRealizationValid dispositionValid.

Definition decideStorageFailureCannotFailByFacts : bool := true.

Definition decideStorageFailureMapsToSourceByFacts
  (failureIdentityValid failureDeclared : bool) : bool :=
  andb failureIdentityValid failureDeclared.

Definition decideStorageFailureProvedUnreachableByFacts
  (evidenceIdentityValid : bool) : bool :=
  evidenceIdentityValid.

Definition decideStorageFailureAssumptionByFacts
  (assumptionIdentityValid : bool) : bool :=
  assumptionIdentityValid.

Definition decideStorageFailureDeploymentRequirementByFacts
  (requirementIdentityValid : bool) : bool :=
  requirementIdentityValid.

Definition decideStorageFailureUnaccountedByFacts : bool := false.

Theorem decideStorageFailureRealizationByFacts_classifies :
  forall facts baseRealizationValid dispositionValid,
    (baseRealizationValid = true <->
      StorageRealizationValid (storageFailureBase facts)) ->
    (dispositionValid = true <->
      StorageFailureDispositionValid
        (storageFailureSourceSurface facts)
        (storageFailurePhysicalFailure facts)) ->
    decideStorageFailureRealizationByFacts
      baseRealizationValid dispositionValid = true <->
    StorageFailureRealizationValid facts.
Proof.
  intros facts baseRealizationValid dispositionValid Hbase Hdisposition.
  unfold decideStorageFailureRealizationByFacts.
  rewrite andb_true_iff.
  unfold StorageFailureRealizationValid.
  split.
  - intros [HbaseBool HdispositionBool].
    split.
    + apply (proj1 Hbase).
      exact HbaseBool.
    + apply (proj1 Hdisposition).
      exact HdispositionBool.
  - intros [HbaseValid HdispositionValid].
    split.
    + apply (proj2 Hbase).
      exact HbaseValid.
    + apply (proj2 Hdisposition).
      exact HdispositionValid.
Qed.

Theorem decideStorageFailureCannotFailByFacts_classifies :
  forall surface,
    decideStorageFailureCannotFailByFacts = true <->
    StorageFailureDispositionValid surface PhysicalAllocationCannotFail.
Proof.
  intros surface.
  unfold decideStorageFailureCannotFailByFacts,
    StorageFailureDispositionValid.
  simpl.
  split.
  - intros _.
    exact I.
  - intros _.
    reflexivity.
Qed.

Theorem decideStorageFailureMapsToSourceByFacts_classifies :
  forall surface failure failureIdentityValid failureDeclared,
    (failureIdentityValid = true <-> failure <> 0) ->
    (failureDeclared = true <->
      sourceFailureContains failure surface = true) ->
    decideStorageFailureMapsToSourceByFacts
      failureIdentityValid failureDeclared = true <->
    StorageFailureDispositionValid
      surface
      (PhysicalAllocationMayFail (StorageFailureMapsToSource failure)).
Proof.
  intros surface failure failureIdentityValid failureDeclared
    Hidentity Hdeclared.
  unfold decideStorageFailureMapsToSourceByFacts.
  rewrite andb_true_iff.
  unfold StorageFailureDispositionValid.
  simpl.
  split.
  - intros [HidentityBool HdeclaredBool].
    split.
    + apply (proj1 Hidentity).
      exact HidentityBool.
    + apply (proj1 Hdeclared).
      exact HdeclaredBool.
  - intros [HidentityValid HdeclaredValid].
    split.
    + apply (proj2 Hidentity).
      exact HidentityValid.
    + apply (proj2 Hdeclared).
      exact HdeclaredValid.
Qed.

Theorem decideStorageFailureProvedUnreachableByFacts_classifies :
  forall surface evidence evidenceIdentityValid,
    (evidenceIdentityValid = true <-> evidence <> 0) ->
    decideStorageFailureProvedUnreachableByFacts evidenceIdentityValid = true <->
    StorageFailureDispositionValid
      surface
      (PhysicalAllocationMayFail
        (StorageFailureProvedUnreachable evidence)).
Proof.
  intros surface evidence evidenceIdentityValid Hidentity.
  unfold decideStorageFailureProvedUnreachableByFacts,
    StorageFailureDispositionValid.
  simpl.
  exact Hidentity.
Qed.

Theorem decideStorageFailureAssumptionByFacts_classifies :
  forall surface assumption assumptionIdentityValid,
    (assumptionIdentityValid = true <-> assumption <> 0) ->
    decideStorageFailureAssumptionByFacts assumptionIdentityValid = true <->
    StorageFailureDispositionValid
      surface
      (PhysicalAllocationMayFail (StorageFailureAssumption assumption)).
Proof.
  intros surface assumption assumptionIdentityValid Hidentity.
  unfold decideStorageFailureAssumptionByFacts,
    StorageFailureDispositionValid.
  simpl.
  exact Hidentity.
Qed.

Theorem decideStorageFailureDeploymentRequirementByFacts_classifies :
  forall surface requirement requirementIdentityValid,
    (requirementIdentityValid = true <-> requirement <> 0) ->
    decideStorageFailureDeploymentRequirementByFacts
      requirementIdentityValid = true <->
    StorageFailureDispositionValid
      surface
      (PhysicalAllocationMayFail
        (StorageFailureDeploymentRequirement requirement)).
Proof.
  intros surface requirement requirementIdentityValid Hidentity.
  unfold decideStorageFailureDeploymentRequirementByFacts,
    StorageFailureDispositionValid.
  simpl.
  exact Hidentity.
Qed.

Theorem decideStorageFailureUnaccountedByFacts_classifies :
  forall surface,
    decideStorageFailureUnaccountedByFacts = true <->
    StorageFailureDispositionValid
      surface
      (PhysicalAllocationMayFail StorageFailureUnaccounted).
Proof.
  intros surface.
  unfold decideStorageFailureUnaccountedByFacts,
    StorageFailureDispositionValid.
  simpl.
  split.
  - intros Hfalse.
    discriminate Hfalse.
  - intros Hfalse.
    contradiction.
Qed.
