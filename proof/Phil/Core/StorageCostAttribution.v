From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import
  StorageRealization
  SystemsRuntimeGraph.

(*
  PHIL-MEM-COST-001 — storage realization cost lineage remains attached to
  the exact semantic subject and exact physical storage domain, while the
  generic Systems runtime-cost graph supplies nonduplication and compatible
  shared-charge rules.

  This normalized model intentionally does not assign universal numeric costs.
  Cost class/shape and the concrete meanings of allocation count, peak live
  memory, bytes copied, residency, and cleanup references remain selected
  ADR-011 profile data and Haskell correspondence boundaries.
*)

Definition StorageResidencyRef := nat.
Definition StorageCleanupRef := nat.

Record StorageCostLineageFacts : Type := mkStorageCostLineageFacts {
  storageLineageSubject : StorageSemanticSubject;
  storageLineagePhysicalObjects : PhysicalStorageObjectKey -> bool;
  storageLineageCostClass : GraphCostClass;
  storageLineageCostShape : GraphCostShape;
  storageLineageAllocationCountPresent : bool;
  storageLineagePeakLiveMemoryPresent : bool;
  storageLineageBytesCopiedPresent : bool;
  storageLineageResidencyRef : StorageResidencyRef -> bool;
  storageLineageCleanupRef : StorageCleanupRef -> bool
}.

Definition StorageCostSubjectExact
  (realization : StorageRealizationFacts)
  (lineage : StorageCostLineageFacts) : Prop :=
  match storageRealizationSubject realization with
  | ExactStorageSemanticSubject subject =>
      storageLineageSubject lineage = subject
  | PhysicalStorageCoincidence _ => False
  end.

Definition StorageCostPhysicalDomainExact
  (realization : StorageRealizationFacts)
  (lineage : StorageCostLineageFacts) : Prop :=
  forall object,
    storageLineagePhysicalObjects lineage object =
      storageRealizationPhysicalObjects realization object.

Definition AttributableStorageCost
  (lineage : StorageCostLineageFacts) : Prop :=
  storageLineageAllocationCountPresent lineage = true \/
  storageLineagePeakLiveMemoryPresent lineage = true \/
  storageLineageBytesCopiedPresent lineage = true \/
  (exists residency,
    storageLineageResidencyRef lineage residency = true) \/
  (exists cleanup,
    storageLineageCleanupRef lineage cleanup = true).

Record StorageCostLineageValid
  (realization : StorageRealizationFacts)
  (lineage : StorageCostLineageFacts) : Prop := mkStorageCostLineageValid {
  storageCostSubjectExact : StorageCostSubjectExact realization lineage;
  storageCostPhysicalDomainExact :
    StorageCostPhysicalDomainExact realization lineage;
  storageCostHasAttributableFact : AttributableStorageCost lineage
}.

Theorem storage_cost_lineage_preserves_exact_subject :
  forall realization lineage subject,
    StorageCostLineageValid realization lineage ->
    storageRealizationSubject realization =
      ExactStorageSemanticSubject subject ->
    storageLineageSubject lineage = subject.
Proof.
  intros realization lineage subject Hvalid Hsubject.
  destruct Hvalid as [Hexact _ _].
  unfold StorageCostSubjectExact in Hexact.
  rewrite Hsubject in Hexact.
  exact Hexact.
Qed.

Theorem storage_cost_lineage_preserves_exact_physical_domain :
  forall realization lineage object,
    StorageCostLineageValid realization lineage ->
    storageLineagePhysicalObjects lineage object =
      storageRealizationPhysicalObjects realization object.
Proof.
  intros realization lineage object Hvalid.
  exact (storageCostPhysicalDomainExact realization lineage Hvalid object).
Qed.

Theorem storage_cost_subject_mismatch_rejects_lineage :
  forall realization lineage subject,
    storageRealizationSubject realization =
      ExactStorageSemanticSubject subject ->
    storageLineageSubject lineage <> subject ->
    ~ StorageCostLineageValid realization lineage.
Proof.
  intros realization lineage subject Hsubject Hmismatch Hvalid.
  apply Hmismatch.
  eapply storage_cost_lineage_preserves_exact_subject; eauto.
Qed.

Theorem storage_cost_physical_domain_mismatch_rejects_lineage :
  forall realization lineage object,
    storageLineagePhysicalObjects lineage object <>
      storageRealizationPhysicalObjects realization object ->
    ~ StorageCostLineageValid realization lineage.
Proof.
  intros realization lineage object Hmismatch Hvalid.
  apply Hmismatch.
  eapply storage_cost_lineage_preserves_exact_physical_domain; eauto.
Qed.

Theorem missing_storage_cost_attribution_rejects_lineage :
  forall realization lineage,
    storageLineageAllocationCountPresent lineage = false ->
    storageLineagePeakLiveMemoryPresent lineage = false ->
    storageLineageBytesCopiedPresent lineage = false ->
    (forall residency,
      storageLineageResidencyRef lineage residency = false) ->
    (forall cleanup,
      storageLineageCleanupRef lineage cleanup = false) ->
    ~ StorageCostLineageValid realization lineage.
Proof.
  intros realization lineage Hallocation Hpeak Hcopied Hresidency Hcleanup Hvalid.
  destruct Hvalid as [_ _ Hattributable].
  unfold AttributableStorageCost in Hattributable.
  destruct Hattributable as
    [HallocationPresent |
     [HpeakPresent |
      [HcopiedPresent |
       [HresidencyPresent | HcleanupPresent]]]].
  - rewrite Hallocation in HallocationPresent. discriminate.
  - rewrite Hpeak in HpeakPresent. discriminate.
  - rewrite Hcopied in HcopiedPresent. discriminate.
  - destruct HresidencyPresent as [residency Hpresent].
    rewrite Hresidency in Hpresent. discriminate.
  - destruct HcleanupPresent as [cleanup Hpresent].
    rewrite Hcleanup in Hpresent. discriminate.
Qed.

(* A storage cost contribution enters the already-certified Systems graph by
   exact contribution/charge identity and exact selected class/shape. *)
Record StorageRuntimeCostBinding
  (graph : RuntimeClaimCostGraph)
  (lineage : StorageCostLineageFacts) : Type := mkStorageRuntimeCostBinding {
  storageRuntimeContribution : GraphContributionId;
  storageRuntimeCharge : GraphChargeId;
  storageRuntimeContributionInCharge :
    ContributionInCharge graph storageRuntimeContribution storageRuntimeCharge;
  storageRuntimeClassExact :
    graphContributionClass graph storageRuntimeContribution =
      storageLineageCostClass lineage;
  storageRuntimeShapeExact :
    graphContributionShape graph storageRuntimeContribution =
      storageLineageCostShape lineage
}.

Theorem storage_runtime_contribution_has_one_final_charge :
  forall graph lineage
         (binding : StorageRuntimeCostBinding graph lineage)
         firstCharge secondCharge,
    ContributionInCharge graph
      (storageRuntimeContribution graph lineage binding) firstCharge ->
    ContributionInCharge graph
      (storageRuntimeContribution graph lineage binding) secondCharge ->
    firstCharge = secondCharge.
Proof.
  intros graph lineage binding firstCharge secondCharge Hfirst Hsecond.
  eapply contribution_has_exactly_one_charge_identity; eauto.
Qed.

Theorem shared_storage_charge_requires_exact_cost_class :
  forall graph firstLineage secondLineage
         (firstBinding : StorageRuntimeCostBinding graph firstLineage)
         (secondBinding : StorageRuntimeCostBinding graph secondLineage),
    RuntimeClaimCostGraphValid graph ->
    storageRuntimeCharge graph firstLineage firstBinding =
      storageRuntimeCharge graph secondLineage secondBinding ->
    storageLineageCostClass firstLineage =
      storageLineageCostClass secondLineage.
Proof.
  intros graph firstLineage secondLineage firstBinding secondBinding
    Hgraph Hcharge.
  destruct firstBinding as
    [firstContribution firstCharge HfirstIn HfirstClass HfirstShape].
  destruct secondBinding as
    [secondContribution secondCharge HsecondIn HsecondClass HsecondShape].
  simpl in Hcharge, HfirstIn, HfirstClass, HsecondIn, HsecondClass.
  subst secondCharge.
  rewrite <- HfirstClass, <- HsecondClass.
  eapply shared_charge_requires_exact_cost_class; eauto.
Qed.

Theorem shared_storage_charge_requires_exact_cost_shape :
  forall graph firstLineage secondLineage
         (firstBinding : StorageRuntimeCostBinding graph firstLineage)
         (secondBinding : StorageRuntimeCostBinding graph secondLineage),
    RuntimeClaimCostGraphValid graph ->
    storageRuntimeCharge graph firstLineage firstBinding =
      storageRuntimeCharge graph secondLineage secondBinding ->
    storageLineageCostShape firstLineage =
      storageLineageCostShape secondLineage.
Proof.
  intros graph firstLineage secondLineage firstBinding secondBinding
    Hgraph Hcharge.
  destruct firstBinding as
    [firstContribution firstCharge HfirstIn HfirstClass HfirstShape].
  destruct secondBinding as
    [secondContribution secondCharge HsecondIn HsecondClass HsecondShape].
  simpl in Hcharge, HfirstIn, HfirstShape, HsecondIn, HsecondShape.
  subst secondCharge.
  rewrite <- HfirstShape, <- HsecondShape.
  eapply shared_charge_requires_exact_cost_shape; eauto.
Qed.

(* Different selected storage strategies and physical domains may carry
   different valid cost lineage while preserving the exact source semantic
   identity. *)
Theorem alternate_storage_strategies_preserve_semantic_identity :
  forall subject semanticRevision outcomeRevision instance
         firstSelected secondSelected firstStrategy secondStrategy
         firstObjects secondObjects,
    storage_semantic_identity
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        firstStrategy firstObjects instance firstSelected) =
    storage_semantic_identity
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        secondStrategy secondObjects instance secondSelected).
Proof.
  intros.
  apply allocation_strategy_is_nonsemantic.
Qed.

Theorem distinct_storage_cost_lineage_does_not_rewrite_semantic_identity :
  forall subject semanticRevision outcomeRevision instance
         firstSelected secondSelected firstStrategy secondStrategy
         firstObjects secondObjects
         (firstLineage secondLineage : StorageCostLineageFacts),
    firstLineage <> secondLineage ->
    storage_semantic_identity
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        firstStrategy firstObjects instance firstSelected) =
    storage_semantic_identity
      (makeStorageRealization
        subject semanticRevision outcomeRevision
        secondStrategy secondObjects instance secondSelected) /\
    firstLineage <> secondLineage.
Proof.
  intros subject semanticRevision outcomeRevision instance
    firstSelected secondSelected firstStrategy secondStrategy
    firstObjects secondObjects firstLineage secondLineage Hdistinct.
  split.
  - apply allocation_strategy_is_nonsemantic.
  - exact Hdistinct.
Qed.

Record CertifiedStorageCostAttribution
  (identity : StageClosureIdentityFacts)
  (liveStrengthenings : RealizationFactSet)
  (strengthenings : StrengtheningEnvironment)
  (liveStaging : StagingRequirementSet)
  (staging : StagingEventEnvironment)
  (liveNextStage : NextStageBasisSet)
  (nextStage : NextStageRequirementEnvironment)
  (realization : StorageRealizationFacts)
  (graph : RuntimeClaimCostGraph)
  (lineage : StorageCostLineageFacts)
  (binding : StorageRuntimeCostBinding graph lineage) : Prop :=
  mkCertifiedStorageCostAttribution {
    certifiedStorageCostRealization :
      CertifiedStorageRealization
        identity liveStrengthenings strengthenings
        liveStaging staging liveNextStage nextStage realization;
    certifiedStorageCostRuntimeGraph : RuntimeClaimCostGraphValid graph;
    certifiedStorageCostLineage : StorageCostLineageValid realization lineage
  }.

Theorem certified_storage_cost_attribution_has_exact_lineage :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage realization graph lineage binding,
    CertifiedStorageCostAttribution
      identity liveStrengthenings strengthenings liveStaging staging
      liveNextStage nextStage realization graph lineage binding ->
    StorageCostSubjectExact realization lineage /\
    StorageCostPhysicalDomainExact realization lineage /\
    AttributableStorageCost lineage.
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage realization graph lineage binding Hcertified.
  destruct Hcertified as [_ _ Hlineage].
  destruct Hlineage as [Hsubject Hdomain Hattributable].
  repeat split; assumption.
Qed.

Theorem certified_storage_cost_attribution_preserves_semantic_identity :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage realization graph lineage binding,
    CertifiedStorageCostAttribution
      identity liveStrengthenings strengthenings liveStaging staging
      liveNextStage nextStage realization graph lineage binding ->
    exists semanticIdentity,
      storage_semantic_identity realization = Some semanticIdentity.
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage realization graph lineage binding Hcertified.
  destruct Hcertified as [Hrealization _ _].
  eapply certified_storage_realization_has_exact_semantic_identity.
  exact Hrealization.
Qed.

Theorem certified_storage_cost_contribution_is_not_double_charged :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage realization graph lineage binding
         firstCharge secondCharge,
    CertifiedStorageCostAttribution
      identity liveStrengthenings strengthenings liveStaging staging
      liveNextStage nextStage realization graph lineage binding ->
    ContributionInCharge graph
      (storageRuntimeContribution graph lineage binding) firstCharge ->
    ContributionInCharge graph
      (storageRuntimeContribution graph lineage binding) secondCharge ->
    firstCharge = secondCharge.
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage realization graph lineage binding
    firstCharge secondCharge Hcertified Hfirst Hsecond.
  eapply storage_runtime_contribution_has_one_final_charge; eauto.
Qed.
