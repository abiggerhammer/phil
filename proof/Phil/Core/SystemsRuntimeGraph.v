From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

From Phil.Systems Require Import Runtime.
From Phil.Core Require Import RuntimePrimitiveIdentity.

(*
  PHIL-SYS-RUNTIME-GRAPH-001 — many-to-many runtime claim/site graph,
  reusable primitive identity, and exact shared-cost attribution.

  This normalized model composes two target-neutral Certified foundations rather
  than rebuilding them:

  - PHIL-SYS-RUNTIME-001 supplies exact selected RuntimeEnforced evidence,
    revision, declared cost, and runtime-site verification;
  - PHIL-TARGET-RUNTIME-PRIM-001 supplies the rule that target-visible runtime
    entry identity depends on physical primitive/profile identity rather than
    assurance metadata or claim-set cardinality.

  Linker symbols, WebAssembly imports/functions/tables, VM opcodes/precompiles,
  SBF syscalls/CPI targets, and other backend entry representations are target
  refinements of that second relation rather than assumptions imported here.

  Concrete Text/Map/Set encoding, canonical stage serialization, selected
  profile vocabulary, and Haskell graph construction remain correspondence
  boundaries exercised by the unchanged SYS-015/016/018 corpora.
*)

Definition GraphClaimId := nat.
Definition GraphSiteId := nat.
Definition GraphSubjectId := nat.
Definition GraphPrimitiveProfileId := nat.
Definition GraphContributionId := nat.
Definition GraphChargeId := nat.
Definition GraphCostClass := nat.
Definition GraphCostShape := nat.

Record RuntimeClaimCostGraph : Type := mkRuntimeClaimCostGraph {
  graphRuntimeEnvironment : RuntimeEvidenceEnvironment;
  graphRuntimeSite : GraphSiteId -> RuntimeSite;
  graphClaimAtSite : GraphClaimId -> GraphSiteId -> Prop;
  graphSiteSubject : GraphSiteId -> GraphSubjectId;
  graphSitePrimitiveProfile : GraphSiteId -> GraphPrimitiveProfileId;
  graphSiteContribution : GraphSiteId -> GraphContributionId;
  graphContributionCharge : GraphContributionId -> GraphChargeId;
  graphContributionClass : GraphContributionId -> GraphCostClass;
  graphContributionShape : GraphContributionId -> GraphCostShape;
  graphRuntimePrimitiveIdentityModel :
    GraphSiteId -> RuntimePrimitiveIdentityModel
}.

Definition ClaimContribution
  (graph : RuntimeClaimCostGraph)
  (claim : GraphClaimId)
  (contribution : GraphContributionId) : Prop :=
  exists site,
    graphClaimAtSite graph claim site /\
    graphSiteContribution graph site = contribution.

Definition ContributionInCharge
  (graph : RuntimeClaimCostGraph)
  (contribution : GraphContributionId)
  (charge : GraphChargeId) : Prop :=
  graphContributionCharge graph contribution = charge.

Definition ClaimCharge
  (graph : RuntimeClaimCostGraph)
  (claim : GraphClaimId)
  (charge : GraphChargeId) : Prop :=
  exists contribution,
    ClaimContribution graph claim contribution /\
    ContributionInCharge graph contribution charge.

Record RuntimeClaimCostGraphValid
  (graph : RuntimeClaimCostGraph) : Prop := mkRuntimeClaimCostGraphValid {
  graphEverySiteVerified :
    forall site,
      RuntimeSiteVerificationSuccess
        (graphRuntimeEnvironment graph)
        (graphRuntimeSite graph site);

  (* Site-owned contribution identity is injective.  Reusing one primitive or
     profile cannot collapse two semantic sites into one contribution. *)
  graphContributionIdentifiesSite :
    forall left right,
      graphSiteContribution graph left = graphSiteContribution graph right ->
      left = right;

  (* A final physical/accounting charge may aggregate several contributions
     only when their selected class and shape agree exactly. *)
  graphSharedChargeClassCompatible :
    forall left right,
      graphContributionCharge graph left = graphContributionCharge graph right ->
      graphContributionClass graph left = graphContributionClass graph right;
  graphSharedChargeShapeCompatible :
    forall left right,
      graphContributionCharge graph left = graphContributionCharge graph right ->
      graphContributionShape graph left = graphContributionShape graph right;

  (* Each site's target-visible runtime entry remains governed by the
     target-neutral runtime primitive identity theorem. *)
  graphEveryRuntimePrimitiveIdentityVerified :
    forall site,
      RuntimePrimitiveIdentityVerificationSuccess
        (graphRuntimePrimitiveIdentityModel graph site)
}.

Theorem graph_site_uses_selected_runtime_evidence :
  forall graph site,
    RuntimeClaimCostGraphValid graph ->
    runtimeEvidenceSelected
      (graphRuntimeEnvironment graph)
      (runtimeSiteEvidence (graphRuntimeSite graph site)) = true.
Proof.
  intros graph site Hvalid.
  eapply verified_runtime_site_uses_selected_evidence.
  exact (graphEverySiteVerified graph Hvalid site).
Qed.

Theorem graph_site_preserves_runtime_revision :
  forall graph site,
    RuntimeClaimCostGraphValid graph ->
    runtimeEvidenceRevision
      (graphRuntimeEnvironment graph)
      (runtimeSiteEvidence (graphRuntimeSite graph site)) =
    Some (runtimeSiteRevision (graphRuntimeSite graph site)).
Proof.
  intros graph site Hvalid.
  eapply verified_runtime_site_preserves_revision.
  exact (graphEverySiteVerified graph Hvalid site).
Qed.

Theorem graph_site_uses_exact_declared_runtime_cost :
  forall graph site,
    RuntimeClaimCostGraphValid graph ->
    runtimeEvidenceDeclaresCost
      (graphRuntimeEnvironment graph)
      (runtimeSiteEvidence (graphRuntimeSite graph site))
      (runtimeSiteCost (graphRuntimeSite graph site)) = true.
Proof.
  intros graph site Hvalid.
  eapply verified_runtime_site_uses_declared_cost.
  exact (graphEverySiteVerified graph Hvalid site).
Qed.

(* One physical semantic site may support several exact claims.  The claims
   remain distinct, but they derive the same site-owned contribution and hence
   the same final charge for that shared work. *)
Theorem one_site_can_support_multiple_claims_with_one_charge :
  forall graph firstClaim secondClaim site,
    firstClaim <> secondClaim ->
    graphClaimAtSite graph firstClaim site ->
    graphClaimAtSite graph secondClaim site ->
    exists contribution charge,
      ClaimContribution graph firstClaim contribution /\
      ClaimContribution graph secondClaim contribution /\
      ClaimCharge graph firstClaim charge /\
      ClaimCharge graph secondClaim charge /\
      firstClaim <> secondClaim.
Proof.
  intros graph firstClaim secondClaim site Hdistinct Hfirst Hsecond.
  exists (graphSiteContribution graph site).
  exists (graphContributionCharge graph (graphSiteContribution graph site)).
  repeat split.
  - exists site. split; [exact Hfirst | reflexivity].
  - exists site. split; [exact Hsecond | reflexivity].
  - exists (graphSiteContribution graph site).
    split.
    + exists site. split; [exact Hfirst | reflexivity].
    + unfold ContributionInCharge. reflexivity.
  - exists (graphSiteContribution graph site).
    split.
    + exists site. split; [exact Hsecond | reflexivity].
    + unfold ContributionInCharge. reflexivity.
  - exact Hdistinct.
Qed.

(* One claim may depend on several cooperating sites.  The claim identity does
   not merge those sites or their contribution lineage. *)
Theorem one_claim_can_depend_on_multiple_distinct_site_contributions :
  forall graph claim firstSite secondSite,
    RuntimeClaimCostGraphValid graph ->
    firstSite <> secondSite ->
    graphClaimAtSite graph claim firstSite ->
    graphClaimAtSite graph claim secondSite ->
    graphSiteContribution graph firstSite <>
      graphSiteContribution graph secondSite.
Proof.
  intros graph claim firstSite secondSite Hvalid Hsites Hfirst Hsecond Heq.
  apply Hsites.
  eapply graphContributionIdentifiesSite.
  - exact Hvalid.
  - exact Heq.
Qed.

(* Reusing one primitive/profile is explicitly weaker than semantic-site or
   contribution identity. *)
Theorem reusable_profile_does_not_collapse_distinct_sites :
  forall graph firstSite secondSite,
    RuntimeClaimCostGraphValid graph ->
    firstSite <> secondSite ->
    graphSitePrimitiveProfile graph firstSite =
      graphSitePrimitiveProfile graph secondSite ->
    graphSiteContribution graph firstSite <>
      graphSiteContribution graph secondSite.
Proof.
  intros graph firstSite secondSite Hvalid Hsites Hprofile Heq.
  apply Hsites.
  eapply graphContributionIdentifiesSite.
  - exact Hvalid.
  - exact Heq.
Qed.

Theorem reusable_profile_does_not_collapse_distinct_subjects :
  forall graph firstSite secondSite,
    graphSitePrimitiveProfile graph firstSite =
      graphSitePrimitiveProfile graph secondSite ->
    graphSiteSubject graph firstSite <>
      graphSiteSubject graph secondSite ->
    graphSiteSubject graph firstSite <>
      graphSiteSubject graph secondSite.
Proof.
  intros graph firstSite secondSite Hprofile Hsubjects.
  exact Hsubjects.
Qed.

(* Contribution -> charge is functional.  A contribution can never be counted
   under two distinct final charge identities. *)
Theorem contribution_has_exactly_one_charge_identity :
  forall graph contribution firstCharge secondCharge,
    ContributionInCharge graph contribution firstCharge ->
    ContributionInCharge graph contribution secondCharge ->
    firstCharge = secondCharge.
Proof.
  intros graph contribution firstCharge secondCharge Hfirst Hsecond.
  unfold ContributionInCharge in Hfirst, Hsecond.
  rewrite Hfirst in Hsecond.
  exact Hsecond.
Qed.

Theorem shared_charge_requires_exact_cost_class :
  forall graph firstContribution secondContribution charge,
    RuntimeClaimCostGraphValid graph ->
    ContributionInCharge graph firstContribution charge ->
    ContributionInCharge graph secondContribution charge ->
    graphContributionClass graph firstContribution =
      graphContributionClass graph secondContribution.
Proof.
  intros graph firstContribution secondContribution charge Hvalid Hfirst Hsecond.
  unfold ContributionInCharge in Hfirst, Hsecond.
  eapply graphSharedChargeClassCompatible.
  - exact Hvalid.
  - rewrite Hfirst, Hsecond. reflexivity.
Qed.

Theorem shared_charge_requires_exact_cost_shape :
  forall graph firstContribution secondContribution charge,
    RuntimeClaimCostGraphValid graph ->
    ContributionInCharge graph firstContribution charge ->
    ContributionInCharge graph secondContribution charge ->
    graphContributionShape graph firstContribution =
      graphContributionShape graph secondContribution.
Proof.
  intros graph firstContribution secondContribution charge Hvalid Hfirst Hsecond.
  unfold ContributionInCharge in Hfirst, Hsecond.
  eapply graphSharedChargeShapeCompatible.
  - exact Hvalid.
  - rewrite Hfirst, Hsecond. reflexivity.
Qed.

Theorem incompatible_cost_class_cannot_share_charge :
  forall graph firstContribution secondContribution charge,
    RuntimeClaimCostGraphValid graph ->
    graphContributionClass graph firstContribution <>
      graphContributionClass graph secondContribution ->
    ~ (ContributionInCharge graph firstContribution charge /\
       ContributionInCharge graph secondContribution charge).
Proof.
  intros graph firstContribution secondContribution charge Hvalid Hdifferent Hshared.
  destruct Hshared as [Hfirst Hsecond].
  apply Hdifferent.
  eapply shared_charge_requires_exact_cost_class; eauto.
Qed.

Theorem incompatible_cost_shape_cannot_share_charge :
  forall graph firstContribution secondContribution charge,
    RuntimeClaimCostGraphValid graph ->
    graphContributionShape graph firstContribution <>
      graphContributionShape graph secondContribution ->
    ~ (ContributionInCharge graph firstContribution charge /\
       ContributionInCharge graph secondContribution charge).
Proof.
  intros graph firstContribution secondContribution charge Hvalid Hdifferent Hshared.
  destruct Hshared as [Hfirst Hsecond].
  apply Hdifferent.
  eapply shared_charge_requires_exact_cost_shape; eauto.
Qed.

(* Claim->charge is derived through exact site/contribution lineage; claims do
   not directly own physical charge entries. *)
Theorem claim_charge_retains_exact_site_contribution_lineage :
  forall graph claim charge,
    ClaimCharge graph claim charge ->
    exists site contribution,
      graphClaimAtSite graph claim site /\
      graphSiteContribution graph site = contribution /\
      graphContributionCharge graph contribution = charge.
Proof.
  intros graph claim charge Hcharge.
  unfold ClaimCharge in Hcharge.
  destruct Hcharge as [contribution [Hcontribution Hcharge]].
  unfold ClaimContribution in Hcontribution.
  destruct Hcontribution as [site [Hedge Hidentity]].
  exists site, contribution.
  repeat split; assumption.
Qed.

(* The target-neutral primitive theorem makes assurance revision/evidence/use
   identity and claim cardinality non-naming metadata for the physical entry. *)
Theorem claim_set_cardinality_does_not_rename_verified_runtime_entry :
  forall graph site revisionA evidenceA useA countA
         revisionB evidenceB useB countB,
    RuntimeClaimCostGraphValid graph ->
    targetEntryFor (graphRuntimePrimitiveIdentityModel graph site)
      revisionA evidenceA useA countA =
    targetEntryFor (graphRuntimePrimitiveIdentityModel graph site)
      revisionB evidenceB useB countB.
Proof.
  intros graph site revisionA evidenceA useA countA
    revisionB evidenceB useB countB Hvalid.
  apply runtime_primitive_entry_is_independent_of_assurance_metadata.
Qed.

Theorem verified_graph_runtime_entry_uses_physical_primitive_profile :
  forall graph site,
    RuntimeClaimCostGraphValid graph ->
    runtimePrimitiveActualEntry
      (graphRuntimePrimitiveIdentityModel graph site) =
    runtimePrimitiveEntryBuilder
      (graphRuntimePrimitiveIdentityModel graph site)
      (runtimePrimitiveIdentity
        (graphRuntimePrimitiveIdentityModel graph site))
      (runtimePrimitiveProfile
        (graphRuntimePrimitiveIdentityModel graph site)).
Proof.
  intros graph site Hvalid.
  eapply verified_runtime_primitive_uses_physical_identity_and_profile.
  exact (graphEveryRuntimePrimitiveIdentityVerified graph Hvalid site).
Qed.
