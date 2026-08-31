From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import
  ArchitectureIdentity
  SystemsRealizationEffects
  SystemsSubjectAuthority
  ArchitectureRealization.

(*
  PHIL-MEM-REALIZE-001 — storage/allocation realization does not define
  Phil semantic identity.

  This normalized model begins after concrete Text/Map/Set representation.
  It composes three already-certified boundaries:

  - PHIL-SYS-SUBJECT-AUTH-001: semantic subject identity must come from a
    checked subject relation, never runtime/physical coincidence;
  - PHIL-SYS-REALIZE-001: target-only realization effects remain explicit;
  - PHIL-ARCH-REALIZE-001: selected realization may change while preserving
    the exact abstract architecture instance.

  Concrete storage strategy names, physical object identifiers, canonical
  serialization/hashing, allocator/provider truth, and target-specific memory
  facts remain implementation/correspondence boundaries.
*)

Definition SemanticValueKey := nat.
Definition SemanticStorageResourceKey := nat.
Definition PhysicalStorageObjectKey := nat.
Definition PhysicalStorageStrategy := nat.
Definition StorageSemanticRevision := nat.
Definition StorageOutcomeRevision := nat.

Inductive StorageSemanticSubject : Type :=
| OrdinarySemanticValue : SemanticValueKey -> StorageSemanticSubject
| ExplicitSemanticStorageResource :
    SemanticStorageResourceKey -> StorageSemanticSubject.

Inductive StorageSubjectBinding : Type :=
| ExactStorageSemanticSubject : StorageSemanticSubject -> StorageSubjectBinding
| PhysicalStorageCoincidence : PhysicalStorageObjectKey -> StorageSubjectBinding.

Definition storage_subject_binding_admitted
  (binding : StorageSubjectBinding) : Prop :=
  match binding with
  | ExactStorageSemanticSubject _ =>
      subject_basis_admitted CheckedSubjectRelation
  | PhysicalStorageCoincidence _ =>
      subject_basis_admitted RuntimeRepresentationCoincidence
  end.

Record StorageSemanticIdentity : Type := mkStorageSemanticIdentity {
  storageIdentitySubject : StorageSemanticSubject;
  storageIdentitySemanticRevision : StorageSemanticRevision;
  storageIdentityOutcomeRevision : StorageOutcomeRevision
}.

Record StorageRealizationFacts : Type := mkStorageRealizationFacts {
  storageRealizationSubject : StorageSubjectBinding;
  storageRealizationSemanticRevision : StorageSemanticRevision;
  storageRealizationOutcomeRevision : StorageOutcomeRevision;
  storageRealizationPhysicalStrategy : PhysicalStorageStrategy;
  storageRealizationPhysicalObjects : PhysicalStorageObjectKey -> bool;
  storageRealizationArchitectureInstance : ArchitectureInstanceIdentity;
  storageRealizationSelectedSemantics : nat
}.

Definition storage_architecture_realization
  (facts : StorageRealizationFacts) : ArchitectureRealizationRevision :=
  deriveArchitectureRealizationRevision
    (storageRealizationArchitectureInstance facts)
    (storageRealizationSelectedSemantics facts).

Definition storage_semantic_identity
  (facts : StorageRealizationFacts) : option StorageSemanticIdentity :=
  match storageRealizationSubject facts with
  | ExactStorageSemanticSubject subject =>
      Some (mkStorageSemanticIdentity
        subject
        (storageRealizationSemanticRevision facts)
        (storageRealizationOutcomeRevision facts))
  | PhysicalStorageCoincidence _ => None
  end.

Definition StorageRealizationValid (facts : StorageRealizationFacts) : Prop :=
  storage_subject_binding_admitted (storageRealizationSubject facts) /\
  (exists subject,
    storageRealizationSubject facts = ExactStorageSemanticSubject subject) /\
  storageRealizationSemanticRevision facts <> 0 /\
  storageRealizationOutcomeRevision facts <> 0 /\
  storageRealizationPhysicalStrategy facts <> 0 /\
  storageRealizationSelectedSemantics facts <> 0 /\
  (forall object,
    storageRealizationPhysicalObjects facts object = true -> object <> 0).

Definition makeStorageRealization
  (subject : StorageSemanticSubject)
  (semanticRevision : StorageSemanticRevision)
  (outcomeRevision : StorageOutcomeRevision)
  (strategy : PhysicalStorageStrategy)
  (objects : PhysicalStorageObjectKey -> bool)
  (instance : ArchitectureInstanceIdentity)
  (selectedSemantics : nat) : StorageRealizationFacts :=
  mkStorageRealizationFacts
    (ExactStorageSemanticSubject subject)
    semanticRevision
    outcomeRevision
    strategy
    objects
    instance
    selectedSemantics.

Theorem exact_storage_subject_uses_checked_subject_relation :
  forall subject,
    storage_subject_binding_admitted (ExactStorageSemanticSubject subject).
Proof.
  intros subject.
  unfold storage_subject_binding_admitted.
  exact checked_subject_relation_admitted.
Qed.

Theorem physical_storage_coincidence_cannot_establish_semantic_identity :
  forall object,
    ~ storage_subject_binding_admitted (PhysicalStorageCoincidence object).
Proof.
  intros object.
  unfold storage_subject_binding_admitted.
  exact runtime_representation_coincidence_rejected.
Qed.

Theorem allocation_strategy_is_nonsemantic :
  forall subject semanticRevision outcomeRevision instance
         priorSelected replacementSelected
         priorStrategy replacementStrategy
         priorObjects replacementObjects,
    storage_semantic_identity
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        priorStrategy priorObjects instance priorSelected) =
    storage_semantic_identity
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        replacementStrategy replacementObjects instance replacementSelected).
Proof.
  reflexivity.
Qed.

Theorem ordinary_value_allocation_strategy_is_nonsemantic :
  forall value semanticRevision outcomeRevision instance
         priorSelected replacementSelected
         priorStrategy replacementStrategy
         priorObjects replacementObjects,
    storage_semantic_identity
      (makeStorageRealization
        (OrdinarySemanticValue value)
        semanticRevision outcomeRevision
        priorStrategy priorObjects instance priorSelected) =
    storage_semantic_identity
      (makeStorageRealization
        (OrdinarySemanticValue value)
        semanticRevision outcomeRevision
        replacementStrategy replacementObjects instance replacementSelected).
Proof.
  intros.
  apply allocation_strategy_is_nonsemantic.
Qed.

Theorem explicit_storage_resource_strategy_is_nonsemantic :
  forall resource semanticRevision outcomeRevision instance
         priorSelected replacementSelected
         priorStrategy replacementStrategy
         priorObjects replacementObjects,
    storage_semantic_identity
      (makeStorageRealization
        (ExplicitSemanticStorageResource resource)
        semanticRevision outcomeRevision
        priorStrategy priorObjects instance priorSelected) =
    storage_semantic_identity
      (makeStorageRealization
        (ExplicitSemanticStorageResource resource)
        semanticRevision outcomeRevision
        replacementStrategy replacementObjects instance replacementSelected).
Proof.
  intros.
  apply allocation_strategy_is_nonsemantic.
Qed.

Theorem shared_physical_storage_cannot_collapse_distinct_semantic_subjects :
  forall leftSubject rightSubject semanticRevision outcomeRevision instance
         selectedSemantics strategy objects,
    leftSubject <> rightSubject ->
    storage_semantic_identity
      (makeStorageRealization
        leftSubject semanticRevision outcomeRevision
        strategy objects instance selectedSemantics) <>
    storage_semantic_identity
      (makeStorageRealization
        rightSubject semanticRevision outcomeRevision
        strategy objects instance selectedSemantics).
Proof.
  intros leftSubject rightSubject semanticRevision outcomeRevision instance
    selectedSemantics strategy objects Hdistinct Heq.
  simpl in Heq.
  injection Heq as Hidentity.
  apply Hdistinct.
  exact (f_equal storageIdentitySubject Hidentity).
Qed.

Theorem selected_physical_realization_change_is_architectural_not_semantic :
  forall subject semanticRevision outcomeRevision instance
         priorSelected replacementSelected
         priorStrategy replacementStrategy
         priorObjects replacementObjects,
    priorSelected <> replacementSelected ->
    storage_semantic_identity
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        priorStrategy priorObjects instance priorSelected) =
    storage_semantic_identity
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        replacementStrategy replacementObjects instance replacementSelected) /\
    storage_architecture_realization
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        priorStrategy priorObjects instance priorSelected) <>
    storage_architecture_realization
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        replacementStrategy replacementObjects instance replacementSelected).
Proof.
  intros subject semanticRevision outcomeRevision instance
    priorSelected replacementSelected priorStrategy replacementStrategy
    priorObjects replacementObjects Hselected.
  split.
  - reflexivity.
  - simpl.
    apply selected_realization_change_revises_realization.
    exact Hselected.
Qed.

Record CertifiedStorageRealization
  (identity : StageClosureIdentityFacts)
  (liveStrengthenings : RealizationFactSet)
  (strengthenings : StrengtheningEnvironment)
  (liveStaging : StagingRequirementSet)
  (staging : StagingEventEnvironment)
  (liveNextStage : NextStageBasisSet)
  (nextStage : NextStageRequirementEnvironment)
  (facts : StorageRealizationFacts) : Prop :=
  mkCertifiedStorageRealization {
    certifiedStorageSystemsEffects :
      SystemsRealizationEffectsPreserved
        identity liveStrengthenings strengthenings
        liveStaging staging liveNextStage nextStage;
    certifiedStorageRelationValid : StorageRealizationValid facts
  }.

Theorem certified_storage_realization_preserves_explicit_systems_effects :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage facts,
    CertifiedStorageRealization
      identity liveStrengthenings strengthenings liveStaging staging
      liveNextStage nextStage facts ->
    StageClosureIdentityValid identity /\
    ExactTargetStrengtheningCoverage liveStrengthenings strengthenings /\
    ExactStagingEventCoverage liveStaging staging /\
    ExactNextStageRequirementCoverage liveNextStage nextStage.
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage facts Hcertified.
  destruct Hcertified as [Hsystems _].
  exact (systems_realization_effects_are_explicit
    identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage Hsystems).
Qed.

Theorem certified_storage_realization_has_exact_semantic_identity :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage facts,
    CertifiedStorageRealization
      identity liveStrengthenings strengthenings liveStaging staging
      liveNextStage nextStage facts ->
    exists semanticIdentity,
      storage_semantic_identity facts = Some semanticIdentity.
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage facts Hcertified.
  destruct Hcertified as [_ Hvalid].
  destruct Hvalid as [_ [Hexact _]].
  destruct Hexact as [subject Hsubject].
  exists (mkStorageSemanticIdentity
    subject
    (storageRealizationSemanticRevision facts)
    (storageRealizationOutcomeRevision facts)).
  unfold storage_semantic_identity.
  rewrite Hsubject.
  reflexivity.
Qed.

Theorem physical_storage_coincidence_cannot_be_certified :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage facts object,
    storageRealizationSubject facts = PhysicalStorageCoincidence object ->
    ~ CertifiedStorageRealization
        identity liveStrengthenings strengthenings liveStaging staging
        liveNextStage nextStage facts.
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage facts object Hphysical Hcertified.
  destruct Hcertified as [_ Hvalid].
  destruct Hvalid as [Hbinding _].
  rewrite Hphysical in Hbinding.
  exact (physical_storage_coincidence_cannot_establish_semantic_identity
    object Hbinding).
Qed.

Theorem certified_storage_realization_preserves_architecture_instance :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage facts,
    CertifiedStorageRealization
      identity liveStrengthenings strengthenings liveStaging staging
      liveNextStage nextStage facts ->
    realizationRevisionInstanceKey (storage_architecture_realization facts) =
      identityInstanceKey (storageRealizationArchitectureInstance facts) /\
    realizationRevisionInstance (storage_architecture_realization facts) =
      identityInstanceRevision (storageRealizationArchitectureInstance facts).
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage facts _.
  split.
  - unfold storage_architecture_realization.
    apply realization_preserves_exact_architecture_instance_key.
  - unfold storage_architecture_realization.
    apply realization_preserves_exact_architecture_instance_revision.
Qed.
