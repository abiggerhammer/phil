From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import SystemsRuntimeGraph StorageCostAttribution.

(*
  Machine-facing decision surface for PHIL-MEM-COST-001.

  Storage-specific lineage validity is kept separate from the already-Certified
  Systems runtime-cost graph.  The latter remains the authority for unique
  contribution->charge identity and shared-charge class/shape compatibility.
*)

Definition decideStorageCostSubjectExactByFacts
  (subjectExact : bool) : bool :=
  subjectExact.

Definition decideStorageCostPhysicalDomainExactByFacts
  (physicalDomainExact : bool) : bool :=
  physicalDomainExact.

Definition decideAttributableStorageCostByFacts
  (allocationCountPresent peakLiveMemoryPresent bytesCopiedPresent
   residencyRefPresent cleanupRefPresent : bool) : bool :=
  orb allocationCountPresent
    (orb peakLiveMemoryPresent
      (orb bytesCopiedPresent
        (orb residencyRefPresent cleanupRefPresent))).

Definition decideStorageCostLineageValidByFacts
  (subjectExact physicalDomainExact attributableCost : bool) : bool :=
  andb subjectExact (andb physicalDomainExact attributableCost).

Definition StorageRuntimeCostBindingFactsValid
  (graph : RuntimeClaimCostGraph)
  (lineage : StorageCostLineageFacts)
  (contribution : GraphContributionId)
  (charge : GraphChargeId) : Prop :=
  ContributionInCharge graph contribution charge /\
  graphContributionClass graph contribution = storageLineageCostClass lineage /\
  graphContributionShape graph contribution = storageLineageCostShape lineage.

Definition decideStorageRuntimeCostBindingByFacts
  (contributionInCharge classExact shapeExact : bool) : bool :=
  andb contributionInCharge (andb classExact shapeExact).

Definition decideCertifiedStorageCostAttributionByFacts
  (realizationValid runtimeGraphValid lineageValid : bool) : bool :=
  andb realizationValid (andb runtimeGraphValid lineageValid).

Theorem decideStorageCostSubjectExactByFacts_classifies :
  forall realization lineage subjectExact,
    (subjectExact = true <-> StorageCostSubjectExact realization lineage) ->
    decideStorageCostSubjectExactByFacts subjectExact = true <->
    StorageCostSubjectExact realization lineage.
Proof.
  intros realization lineage subjectExact Hsubject.
  unfold decideStorageCostSubjectExactByFacts.
  exact Hsubject.
Qed.

Theorem decideStorageCostPhysicalDomainExactByFacts_classifies :
  forall realization lineage physicalDomainExact,
    (physicalDomainExact = true <->
      StorageCostPhysicalDomainExact realization lineage) ->
    decideStorageCostPhysicalDomainExactByFacts physicalDomainExact = true <->
    StorageCostPhysicalDomainExact realization lineage.
Proof.
  intros realization lineage physicalDomainExact Hdomain.
  unfold decideStorageCostPhysicalDomainExactByFacts.
  exact Hdomain.
Qed.

Theorem decideAttributableStorageCostByFacts_classifies :
  forall lineage allocationCountPresent peakLiveMemoryPresent
         bytesCopiedPresent residencyRefPresent cleanupRefPresent,
    (allocationCountPresent = true <->
      storageLineageAllocationCountPresent lineage = true) ->
    (peakLiveMemoryPresent = true <->
      storageLineagePeakLiveMemoryPresent lineage = true) ->
    (bytesCopiedPresent = true <->
      storageLineageBytesCopiedPresent lineage = true) ->
    (residencyRefPresent = true <->
      exists residency,
        storageLineageResidencyRef lineage residency = true) ->
    (cleanupRefPresent = true <->
      exists cleanup,
        storageLineageCleanupRef lineage cleanup = true) ->
    decideAttributableStorageCostByFacts
      allocationCountPresent peakLiveMemoryPresent bytesCopiedPresent
      residencyRefPresent cleanupRefPresent = true <->
    AttributableStorageCost lineage.
Proof.
  intros lineage allocationCountPresent peakLiveMemoryPresent
    bytesCopiedPresent residencyRefPresent cleanupRefPresent
    Hallocation Hpeak Hcopied Hresidency Hcleanup.
  unfold decideAttributableStorageCostByFacts.
  repeat rewrite orb_true_iff.
  unfold AttributableStorageCost.
  rewrite Hallocation, Hpeak, Hcopied, Hresidency, Hcleanup.
  reflexivity.
Qed.

Theorem decideStorageCostLineageValidByFacts_classifies :
  forall realization lineage subjectExact physicalDomainExact attributableCost,
    (subjectExact = true <-> StorageCostSubjectExact realization lineage) ->
    (physicalDomainExact = true <->
      StorageCostPhysicalDomainExact realization lineage) ->
    (attributableCost = true <-> AttributableStorageCost lineage) ->
    decideStorageCostLineageValidByFacts
      subjectExact physicalDomainExact attributableCost = true <->
    StorageCostLineageValid realization lineage.
Proof.
  intros realization lineage subjectExact physicalDomainExact attributableCost
    Hsubject Hdomain Hattributable.
  unfold decideStorageCostLineageValidByFacts.
  repeat rewrite andb_true_iff.
  split.
  - intros [HsubjectBool [HdomainBool HattributableBool]].
    constructor.
    + apply (proj1 Hsubject). exact HsubjectBool.
    + apply (proj1 Hdomain). exact HdomainBool.
    + apply (proj1 Hattributable). exact HattributableBool.
  - intros Hvalid.
    destruct Hvalid as [HsubjectProp HdomainProp HattributableProp].
    split.
    + apply (proj2 Hsubject). exact HsubjectProp.
    + split.
      * apply (proj2 Hdomain). exact HdomainProp.
      * apply (proj2 Hattributable). exact HattributableProp.
Qed.

Theorem decideStorageRuntimeCostBindingByFacts_classifies :
  forall graph lineage contribution charge
         contributionInCharge classExact shapeExact,
    (contributionInCharge = true <->
      ContributionInCharge graph contribution charge) ->
    (classExact = true <->
      graphContributionClass graph contribution =
        storageLineageCostClass lineage) ->
    (shapeExact = true <->
      graphContributionShape graph contribution =
        storageLineageCostShape lineage) ->
    decideStorageRuntimeCostBindingByFacts
      contributionInCharge classExact shapeExact = true <->
    StorageRuntimeCostBindingFactsValid graph lineage contribution charge.
Proof.
  intros graph lineage contribution charge contributionInCharge classExact
    shapeExact Hin Hclass Hshape.
  unfold decideStorageRuntimeCostBindingByFacts,
    StorageRuntimeCostBindingFactsValid.
  repeat rewrite andb_true_iff.
  rewrite Hin, Hclass, Hshape.
  reflexivity.
Qed.

Theorem decideStorageRuntimeCostBindingByFacts_constructs :
  forall graph lineage contribution charge
         contributionInCharge classExact shapeExact,
    (contributionInCharge = true ->
      ContributionInCharge graph contribution charge) ->
    (classExact = true ->
      graphContributionClass graph contribution =
        storageLineageCostClass lineage) ->
    (shapeExact = true ->
      graphContributionShape graph contribution =
        storageLineageCostShape lineage) ->
    decideStorageRuntimeCostBindingByFacts
      contributionInCharge classExact shapeExact = true ->
    StorageRuntimeCostBinding graph lineage.
Proof.
  intros graph lineage contribution charge contributionInCharge classExact
    shapeExact Hin Hclass Hshape Hdecision.
  unfold decideStorageRuntimeCostBindingByFacts in Hdecision.
  repeat rewrite andb_true_iff in Hdecision.
  destruct Hdecision as [HinBool [HclassBool HshapeBool]].
  refine (mkStorageRuntimeCostBinding
    graph lineage contribution charge
    (Hin HinBool) (Hclass HclassBool) (Hshape HshapeBool)).
Qed.

Theorem decideCertifiedStorageCostAttributionByFacts_classifies :
  forall identity liveStrengthenings strengthenings liveStaging staging
         liveNextStage nextStage realization graph lineage
         (binding : StorageRuntimeCostBinding graph lineage)
         realizationValid runtimeGraphValid lineageValid,
    (realizationValid = true <->
      CertifiedStorageRealization
        identity liveStrengthenings strengthenings liveStaging staging
        liveNextStage nextStage realization) ->
    (runtimeGraphValid = true <-> RuntimeClaimCostGraphValid graph) ->
    (lineageValid = true <-> StorageCostLineageValid realization lineage) ->
    decideCertifiedStorageCostAttributionByFacts
      realizationValid runtimeGraphValid lineageValid = true <->
    CertifiedStorageCostAttribution
      identity liveStrengthenings strengthenings liveStaging staging
      liveNextStage nextStage realization graph lineage binding.
Proof.
  intros identity liveStrengthenings strengthenings liveStaging staging
    liveNextStage nextStage realization graph lineage binding
    realizationValid runtimeGraphValid lineageValid
    Hrealization Hgraph Hlineage.
  unfold decideCertifiedStorageCostAttributionByFacts.
  repeat rewrite andb_true_iff.
  split.
  - intros [HrealizationBool [HgraphBool HlineageBool]].
    constructor.
    + apply (proj1 Hrealization). exact HrealizationBool.
    + apply (proj1 Hgraph). exact HgraphBool.
    + apply (proj1 Hlineage). exact HlineageBool.
  - intros Hcertified.
    destruct Hcertified as [HrealizationProp HgraphProp HlineageProp].
    split.
    + apply (proj2 Hrealization). exact HrealizationProp.
    + split.
      * apply (proj2 Hgraph). exact HgraphProp.
      * apply (proj2 Hlineage). exact HlineageProp.
Qed.
