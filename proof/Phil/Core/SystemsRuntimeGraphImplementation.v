From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import SystemsRuntimeGraph.

(*
  Mechanical implementation-refinement surface for already-Certified
  PHIL-SYS-RUNTIME-GRAPH-001.  The extracted classifiers own only the
  normalized theorem gates.  Concrete Haskell graph/domain construction,
  selected profile data, representation, and diagnostics remain explicit
  correspondence boundaries.
*)

Inductive RuntimeClaimGraphDecision : Type :=
| RuntimeClaimGraphAcceptedDecision
| RuntimeClaimGraphSiteVerificationDecision.

Definition decideRuntimeClaimGraphByFacts
  (allSitesVerified : bool) : RuntimeClaimGraphDecision :=
  if allSitesVerified
  then RuntimeClaimGraphAcceptedDecision
  else RuntimeClaimGraphSiteVerificationDecision.

Theorem runtime_claim_graph_decision_exact :
  forall allSitesVerified,
    decideRuntimeClaimGraphByFacts allSitesVerified =
      RuntimeClaimGraphAcceptedDecision <->
    allSitesVerified = true.
Proof.
  intros allSitesVerified.
  unfold decideRuntimeClaimGraphByFacts.
  destruct allSitesVerified; split; intros H; try reflexivity; discriminate.
Qed.

Inductive RuntimePrimitiveReuseDecision : Type :=
| RuntimePrimitiveReuseAcceptedDecision
| RuntimePrimitiveReuseContributionIdentityDecision
| RuntimePrimitiveReuseSymbolIdentityDecision.

Definition decideRuntimePrimitiveReuseByFacts
  (contributionIdentifiesSite runtimeSymbolsVerified : bool)
  : RuntimePrimitiveReuseDecision :=
  if contributionIdentifiesSite then
    if runtimeSymbolsVerified
    then RuntimePrimitiveReuseAcceptedDecision
    else RuntimePrimitiveReuseSymbolIdentityDecision
  else RuntimePrimitiveReuseContributionIdentityDecision.

Theorem runtime_primitive_reuse_decision_exact :
  forall contributionIdentifiesSite runtimeSymbolsVerified,
    decideRuntimePrimitiveReuseByFacts
      contributionIdentifiesSite runtimeSymbolsVerified =
      RuntimePrimitiveReuseAcceptedDecision <->
    contributionIdentifiesSite = true /\ runtimeSymbolsVerified = true.
Proof.
  intros contributionIdentifiesSite runtimeSymbolsVerified.
  unfold decideRuntimePrimitiveReuseByFacts.
  destruct contributionIdentifiesSite; destruct runtimeSymbolsVerified;
    split; intros H; try discriminate; try (split; reflexivity).
Qed.

Inductive RuntimeCostAttributionDecision : Type :=
| RuntimeCostAttributionAcceptedDecision
| RuntimeCostAttributionClassDecision
| RuntimeCostAttributionShapeDecision.

Definition decideRuntimeCostAttributionByFacts
  (sharedChargeClassCompatible sharedChargeShapeCompatible : bool)
  : RuntimeCostAttributionDecision :=
  if sharedChargeClassCompatible then
    if sharedChargeShapeCompatible
    then RuntimeCostAttributionAcceptedDecision
    else RuntimeCostAttributionShapeDecision
  else RuntimeCostAttributionClassDecision.

Theorem runtime_cost_attribution_decision_exact :
  forall sharedChargeClassCompatible sharedChargeShapeCompatible,
    decideRuntimeCostAttributionByFacts
      sharedChargeClassCompatible sharedChargeShapeCompatible =
      RuntimeCostAttributionAcceptedDecision <->
    sharedChargeClassCompatible = true /\
    sharedChargeShapeCompatible = true.
Proof.
  intros sharedChargeClassCompatible sharedChargeShapeCompatible.
  unfold decideRuntimeCostAttributionByFacts.
  destruct sharedChargeClassCompatible; destruct sharedChargeShapeCompatible;
    split; intros H; try discriminate; try (split; reflexivity).
Qed.

Inductive SystemsRuntimeGraphDecision : Type :=
| SystemsRuntimeGraphAcceptedDecision
| SystemsRuntimeGraphClaimGraphDecision
| SystemsRuntimeGraphPrimitiveReuseDecision
| SystemsRuntimeGraphCostAttributionDecision.

Definition decideSystemsRuntimeGraphByFacts
  (claimGraphAccepted primitiveReuseAccepted costAttributionAccepted : bool)
  : SystemsRuntimeGraphDecision :=
  if claimGraphAccepted then
    if primitiveReuseAccepted then
      if costAttributionAccepted
      then SystemsRuntimeGraphAcceptedDecision
      else SystemsRuntimeGraphCostAttributionDecision
    else SystemsRuntimeGraphPrimitiveReuseDecision
  else SystemsRuntimeGraphClaimGraphDecision.

Theorem systems_runtime_graph_decision_exact :
  forall claimGraphAccepted primitiveReuseAccepted costAttributionAccepted,
    decideSystemsRuntimeGraphByFacts
      claimGraphAccepted primitiveReuseAccepted costAttributionAccepted =
      SystemsRuntimeGraphAcceptedDecision <->
    claimGraphAccepted = true /\ primitiveReuseAccepted = true /\
    costAttributionAccepted = true.
Proof.
  intros claimGraphAccepted primitiveReuseAccepted costAttributionAccepted.
  unfold decideSystemsRuntimeGraphByFacts.
  destruct claimGraphAccepted; destruct primitiveReuseAccepted;
    destruct costAttributionAccepted; split; intros H; try discriminate;
    try (repeat split; reflexivity).
Qed.

Theorem systems_runtime_graph_decision_corresponds_validity :
  forall graph claimGraphAccepted primitiveReuseAccepted costAttributionAccepted,
    (claimGraphAccepted = true <->
      forall site,
        RuntimeSiteVerificationSuccess
          (graphRuntimeEnvironment graph)
          (graphRuntimeSite graph site)) ->
    (primitiveReuseAccepted = true <->
      (forall left right,
        graphSiteContribution graph left = graphSiteContribution graph right ->
        left = right) /\
      (forall site,
        RuntimeSymbolVerificationSuccess (graphRuntimeSymbolModel graph site))) ->
    (costAttributionAccepted = true <->
      (forall left right,
        graphContributionCharge graph left = graphContributionCharge graph right ->
        graphContributionClass graph left = graphContributionClass graph right) /\
      (forall left right,
        graphContributionCharge graph left = graphContributionCharge graph right ->
        graphContributionShape graph left = graphContributionShape graph right)) ->
    decideSystemsRuntimeGraphByFacts
      claimGraphAccepted primitiveReuseAccepted costAttributionAccepted =
      SystemsRuntimeGraphAcceptedDecision <->
    RuntimeClaimCostGraphValid graph.
Proof.
  intros graph claimGraphAccepted primitiveReuseAccepted costAttributionAccepted
    Hclaim Hreuse Hcost.
  split.
  - intros Haccepted.
    apply systems_runtime_graph_decision_exact in Haccepted.
    destruct Haccepted as [HclaimAccepted [HreuseAccepted HcostAccepted]].
    apply Hclaim in HclaimAccepted.
    apply Hreuse in HreuseAccepted.
    apply Hcost in HcostAccepted.
    destruct HreuseAccepted as [Hcontribution Hsymbol].
    destruct HcostAccepted as [Hclass Hshape].
    constructor; assumption.
  - intros Hvalid.
    destruct Hvalid as [Hsite Hcontribution Hclass Hshape Hsymbol].
    apply systems_runtime_graph_decision_exact.
    split.
    + apply Hclaim. exact Hsite.
    + split.
      * apply Hreuse. split; assumption.
      * apply Hcost. split; assumption.
Qed.
