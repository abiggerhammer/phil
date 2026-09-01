From Stdlib Require Import Bool.Bool Lists.List Arith.PeanoNat.
Import ListNotations.

From Phil.Core Require Import ProviderQualificationLineageCore.

(* Mechanical implementation-refinement surface for PHIL-PROV-LINEAGE-CORE-001. *)

Inductive QualificationIdentityDecision : Type :=
| QualificationIdentityAcceptedDecision
| QualificationEvidenceClaimDecision
| QualificationAdmissionClaimDecision
| QualificationAdmissionEvidenceDecision
| QualificationAdmissionInterfaceDecision.

Definition decideQualificationIdentityByFacts
  (evidenceClaimExact admissionClaimExact admissionEvidenceExact
   admissionInterfaceExact : bool) : QualificationIdentityDecision :=
  if evidenceClaimExact then
    if admissionClaimExact then
      if admissionEvidenceExact then
        if admissionInterfaceExact then QualificationIdentityAcceptedDecision
        else QualificationAdmissionInterfaceDecision
      else QualificationAdmissionEvidenceDecision
    else QualificationAdmissionClaimDecision
  else QualificationEvidenceClaimDecision.

Theorem qualification_identity_decision_accepted_iff :
  forall a b c d,
    decideQualificationIdentityByFacts a b c d =
      QualificationIdentityAcceptedDecision <->
    a = true /\ b = true /\ c = true /\ d = true.
Proof.
  intros a b c d.
  destruct a, b, c, d; simpl; intuition discriminate.
Qed.

Definition reflectedQualificationIdentityDecision
  (claim : QualificationClaimIdentity)
  (evidence : QualificationEvidenceIdentity)
  (admission : QualificationAdmissionIdentity) : QualificationIdentityDecision :=
  decideQualificationIdentityByFacts
    (Nat.eqb (lineageEvidenceClaimRevision evidence) (lineageClaimRevision claim))
    (Nat.eqb (lineageAdmissionClaimRevision admission) (lineageClaimRevision claim))
    (Nat.eqb (lineageAdmissionEvidenceRevision admission) (lineageEvidenceRevision evidence))
    (Nat.eqb (lineageAdmissionRequiredInterface admission)
      (lineageClaimRequiredInterface claim)).

Theorem reflected_qualification_identity_decision_exact :
  forall claim evidence admission,
    reflectedQualificationIdentityDecision claim evidence admission =
      QualificationIdentityAcceptedDecision <->
    AdmissionBindsClaimAndEvidence claim evidence admission.
Proof.
  intros claim evidence admission.
  unfold reflectedQualificationIdentityDecision.
  rewrite qualification_identity_decision_accepted_iff.
  unfold AdmissionBindsClaimAndEvidence, EvidenceBindsClaim.
  repeat rewrite Nat.eqb_eq.
  tauto.
Qed.

Inductive QualificationRegistryDecision : Type :=
| QualificationRegistryAcceptedDecision
| QualificationNodeKeyDecision
| QualificationGroundKeyDecision.

Definition decideQualificationRegistryByFacts
  (nodeKeysExact groundKeysExact : bool) : QualificationRegistryDecision :=
  if nodeKeysExact then
    if groundKeysExact then QualificationRegistryAcceptedDecision
    else QualificationGroundKeyDecision
  else QualificationNodeKeyDecision.

Theorem qualification_registry_decision_accepted_iff :
  forall a b,
    decideQualificationRegistryByFacts a b = QualificationRegistryAcceptedDecision <->
    a = true /\ b = true.
Proof.
  intros a b; destruct a, b; simpl; intuition discriminate.
Qed.

Inductive QualificationRootDecision : Type :=
| QualificationRootAcceptedDecision
| QualificationUnknownRootDecision.

Definition decideQualificationRootByFacts (rootKnown : bool)
  : QualificationRootDecision :=
  if rootKnown then QualificationRootAcceptedDecision
  else QualificationUnknownRootDecision.

Inductive QualificationDependencyNodeDecision : Type :=
| QualificationDependencyNodeAcceptedDecision
| QualificationRejectedAdmissionDecision
| QualificationUnknownAdmissionDecision
| QualificationUnknownGroundDecision
| QualificationRejectedGroundDecision.

Definition decideQualificationDependencyNodeByFacts
  (admissionAccepted admissionDependenciesKnown groundsKnown groundsAccepted : bool)
  : QualificationDependencyNodeDecision :=
  if admissionAccepted then
    if admissionDependenciesKnown then
      if groundsKnown then
        if groundsAccepted then QualificationDependencyNodeAcceptedDecision
        else QualificationRejectedGroundDecision
      else QualificationUnknownGroundDecision
    else QualificationUnknownAdmissionDecision
  else QualificationRejectedAdmissionDecision.

Theorem qualification_dependency_node_decision_accepted_iff :
  forall a b c d,
    decideQualificationDependencyNodeByFacts a b c d =
      QualificationDependencyNodeAcceptedDecision <->
    a = true /\ b = true /\ c = true /\ d = true.
Proof.
  intros a b c d; destruct a, b, c, d; simpl; intuition discriminate.
Qed.

Definition propagateGroundPresence
  (ownGroundPresent : bool) (dependencyGroundPresence : list bool) : bool :=
  orb ownGroundPresent (existsb (fun value => value) dependencyGroundPresence).

Lemma existsb_identity_true_iff :
  forall values,
    existsb (fun value => value) values = true <-> In true values.
Proof.
  induction values as [|value tail IH].
  - simpl. intuition discriminate.
  - destruct value; simpl.
    + intuition.
    + split.
      * intro Hexists.
        right.
        apply (proj1 IH).
        exact Hexists.
      * intros [Hfalse | Hin].
        -- discriminate Hfalse.
        -- apply (proj2 IH).
           exact Hin.
Qed.

Theorem propagate_ground_presence_exact :
  forall own dependencies,
    propagateGroundPresence own dependencies = true <->
    own = true \/ In true dependencies.
Proof.
  intros own dependencies.
  unfold propagateGroundPresence.
  destruct own; simpl.
  - intuition.
  - apply existsb_identity_true_iff.
Qed.

Theorem direct_ground_presence_is_preserved :
  forall dependencies,
    propagateGroundPresence true dependencies = true.
Proof.
  intros; reflexivity.
Qed.

Theorem dependency_ground_presence_is_inherited :
  forall own dependencies,
    In true dependencies -> propagateGroundPresence own dependencies = true.
Proof.
  intros own dependencies Hin.
  apply (proj2 (propagate_ground_presence_exact own dependencies)).
  right; exact Hin.
Qed.

Theorem no_ground_cannot_self_endorse :
  forall dependencies,
    ~ In true dependencies ->
    propagateGroundPresence false dependencies = false.
Proof.
  intros dependencies Hnone.
  unfold propagateGroundPresence; simpl.
  destruct (existsb (fun value => value) dependencies) eqn:Hexists.
  - exfalso. apply Hnone.
    apply (proj1 (existsb_identity_true_iff dependencies)). exact Hexists.
  - reflexivity.
Qed.

Inductive QualificationDependencyClosureDecision : Type :=
| QualificationDependencyClosureAcceptedDecision
| QualificationDependencyUngroundedDecision.

Definition decideQualificationDependencyClosureByFacts
  (allReachableGrounded : bool) : QualificationDependencyClosureDecision :=
  if allReachableGrounded then QualificationDependencyClosureAcceptedDecision
  else QualificationDependencyUngroundedDecision.

Theorem qualification_dependency_closure_decision_accepted_iff :
  forall grounded,
    decideQualificationDependencyClosureByFacts grounded =
      QualificationDependencyClosureAcceptedDecision <->
    grounded = true.
Proof.
  intro grounded; destruct grounded; simpl; intuition discriminate.
Qed.
