From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Assurance Require Import EvidenceUse.
From Phil.Systems Require Import Runtime.
From Phil.Core Require Import SystemsRuntimeGraph.

(*
  PHIL-ASSURE-CARRIER-001 — exact RuntimeEnforced carrier establishment,
  coverage, and transfer preservation.

  This normalized model composes two Certified predecessor surfaces:

  - PHIL-ASSURE-EVID-001 supplies the rule that RuntimeEnforced authority is
    available only with a present/complete runtime mechanism, runtime residue,
    and an exact known cost reference;
  - PHIL-SYS-RUNTIME-GRAPH-001 supplies exact selected RuntimeEnforced evidence,
    revision, cost, semantic-site contribution, and final-charge lineage.

  DEP-001 correspondence supplies the exact retained-use -> carrier -> actual
  Systems runtime-site binding. DEP-002 correspondence supplies process-local
  use coverage and the preserve/replace/discharge/end-validity transfer rule.

  Concrete Haskell Map/Set/Text representation, enumeration of potentially
  violating uses, physical mechanism soundness, scheduler/device behavior, and
  provider/platform evidence truth remain explicit correspondence boundaries.
*)

Definition CarrierKey := nat.
Definition CarrierUseId := nat.
Definition CarrierProcessId := nat.
Definition CarrierExecutionId := nat.
Definition CarrierBoundaryId := nat.
Definition CarrierTransitionId := nat.
Definition CarrierObligationId := nat.
Definition CarrierEvidenceId := nat.
Definition CarrierCostRef := nat.

Inductive CarrierUseDisposition : Type :=
| CarrierUseStaticallySafe
| CarrierUseCovered (carrier : CarrierKey)
| CarrierUseExplicitBoundary (boundary : CarrierBoundaryId).

Inductive CarrierTransitionDisposition : Type :=
| CarrierPreserved (carrier : CarrierKey)
| CarrierReplaced (prior next : CarrierKey)
| CarrierDischarged (carrier : CarrierKey)
| CarrierValidityEnded (carrier : CarrierKey).

Record RuntimeCarrierModel : Type := mkRuntimeCarrierModel {
  carrierGraph : RuntimeClaimCostGraph;

  carrierKnown : CarrierKey -> bool;
  carrierRuntimeAuthority : CarrierKey -> RuntimeAuthority;
  carrierObligation : CarrierKey -> CarrierObligationId;
  carrierClaim : CarrierKey -> GraphClaimId;
  carrierProcess : CarrierKey -> CarrierProcessId;
  carrierExecutionCovered : CarrierKey -> CarrierExecutionId -> bool;
  carrierEstablishedAt : CarrierKey -> GraphSiteId -> bool;

  carrierRequiredUse : CarrierUseId -> bool;
  carrierPotentiallyViolatingUse : CarrierUseId -> bool;
  carrierBinding : CarrierUseId -> option CarrierKey;
  carrierUseDisposition : CarrierUseId -> CarrierUseDisposition;
  carrierUseSite : CarrierUseId -> GraphSiteId;
  carrierUseObligation : CarrierUseId -> CarrierObligationId;
  carrierUseEvidence : CarrierUseId -> CarrierEvidenceId;
  carrierUseCost : CarrierUseId -> CarrierCostRef;
  carrierUseProcess : CarrierUseId -> CarrierProcessId;
  carrierUseExecution : CarrierUseId -> CarrierExecutionId;

  carrierTransitionActive : CarrierTransitionId -> bool;
  carrierTransitionDisposition : CarrierTransitionId -> CarrierTransitionDisposition;
  carrierTransitionObligation : CarrierTransitionId -> CarrierObligationId;
  carrierTransitionProcess : CarrierTransitionId -> CarrierProcessId;
  carrierTransitionFrom : CarrierTransitionId -> CarrierExecutionId;
  carrierTransitionTo : CarrierTransitionId -> CarrierExecutionId;
  carrierTransitionDestinationRuntimeBound : CarrierTransitionId -> bool
}.

Definition ExactCarrierBinding
  (model : RuntimeCarrierModel)
  (use : CarrierUseId)
  (carrier : CarrierKey) : Prop :=
  carrierBinding model use = Some carrier /\
  carrierRequiredUse model use = true /\
  carrierKnown model carrier = true /\
  carrierUseDisposition model use = CarrierUseCovered carrier /\
  carrierUseObligation model use = carrierObligation model carrier /\
  runtimeSiteRevision
      (graphRuntimeSite (carrierGraph model) (carrierUseSite model use)) =
    carrierUseObligation model use /\
  runtimeSiteEvidence
      (graphRuntimeSite (carrierGraph model) (carrierUseSite model use)) =
    carrierUseEvidence model use /\
  runtimeSiteCost
      (graphRuntimeSite (carrierGraph model) (carrierUseSite model use)) =
    carrierUseCost model use /\
  carrierEstablishedAt model carrier (carrierUseSite model use) = true /\
  graphClaimAtSite
    (carrierGraph model)
    (carrierClaim model carrier)
    (carrierUseSite model use) /\
  carrierUseProcess model use = carrierProcess model carrier /\
  carrierExecutionCovered model carrier (carrierUseExecution model use) = true /\
  verifyRuntimeAuthority (carrierRuntimeAuthority model carrier) = GateAccepted.

Definition CarrierUseAccounted
  (model : RuntimeCarrierModel)
  (use : CarrierUseId) : Prop :=
  match carrierUseDisposition model use with
  | CarrierUseStaticallySafe => True
  | CarrierUseCovered carrier => ExactCarrierBinding model use carrier
  | CarrierUseExplicitBoundary boundary => boundary <> 0
  end.

Definition CarrierTransitionAccounted
  (model : RuntimeCarrierModel)
  (transition : CarrierTransitionId) : Prop :=
  match carrierTransitionDisposition model transition with
  | CarrierPreserved carrier =>
      carrierKnown model carrier = true /\
      carrierTransitionObligation model transition = carrierObligation model carrier /\
      carrierTransitionProcess model transition = carrierProcess model carrier /\
      carrierExecutionCovered model carrier (carrierTransitionFrom model transition) = true /\
      carrierExecutionCovered model carrier (carrierTransitionTo model transition) = true
  | CarrierReplaced prior next =>
      carrierKnown model prior = true /\
      carrierKnown model next = true /\
      carrierTransitionObligation model transition = carrierObligation model prior /\
      carrierTransitionObligation model transition = carrierObligation model next /\
      carrierTransitionProcess model transition = carrierProcess model prior /\
      carrierTransitionProcess model transition = carrierProcess model next /\
      carrierExecutionCovered model prior (carrierTransitionFrom model transition) = true /\
      carrierExecutionCovered model next (carrierTransitionTo model transition) = true
  | CarrierDischarged carrier =>
      carrierKnown model carrier = true /\
      carrierTransitionObligation model transition = carrierObligation model carrier /\
      carrierTransitionProcess model transition = carrierProcess model carrier /\
      carrierExecutionCovered model carrier (carrierTransitionFrom model transition) = true /\
      carrierTransitionDestinationRuntimeBound model transition = false
  | CarrierValidityEnded carrier =>
      carrierKnown model carrier = true /\
      carrierTransitionObligation model transition = carrierObligation model carrier /\
      carrierTransitionProcess model transition = carrierProcess model carrier /\
      carrierExecutionCovered model carrier (carrierTransitionFrom model transition) = true /\
      carrierTransitionDestinationRuntimeBound model transition = false
  end.

Record RuntimeCarrierCertified
  (model : RuntimeCarrierModel) : Prop := mkRuntimeCarrierCertified {
  carrierGraphCertified : RuntimeClaimCostGraphValid (carrierGraph model);

  carrierEveryRequiredUseBound :
    forall use,
      carrierRequiredUse model use = true ->
      exists carrier, ExactCarrierBinding model use carrier;

  carrierNoPhantomBinding :
    forall use carrier,
      carrierBinding model use = Some carrier ->
      carrierRequiredUse model use = true /\
      carrierKnown model carrier = true;

  carrierEveryPotentialViolationAccounted :
    forall use,
      carrierPotentiallyViolatingUse model use = true ->
      CarrierUseAccounted model use;

  carrierEveryActiveTransitionAccounted :
    forall transition,
      carrierTransitionActive model transition = true ->
      CarrierTransitionAccounted model transition
}.

Theorem certified_required_runtime_use_has_exact_carrier :
  forall model use,
    RuntimeCarrierCertified model ->
    carrierRequiredUse model use = true ->
    exists carrier,
      ExactCarrierBinding model use carrier /\
      carrierKnown model carrier = true.
Proof.
  intros model use Hcert Hrequired.
  destruct Hcert as [Hgraph Hbound Hphantom Huses Htransfers].
  destruct (Hbound use Hrequired) as [carrier Hexact].
  exists carrier.
  split.
  - exact Hexact.
  - destruct Hexact as [_ [_ [Hknown _]]].
    exact Hknown.
Qed.

Theorem certified_required_runtime_use_has_complete_runtime_authority :
  forall model use,
    RuntimeCarrierCertified model ->
    carrierRequiredUse model use = true ->
    exists carrier,
      ExactCarrierBinding model use carrier /\
      runtimeMechanismPresent (carrierRuntimeAuthority model carrier) = true /\
      runtimeMechanismComplete (carrierRuntimeAuthority model carrier) = true /\
      runtimeResiduePresent (carrierRuntimeAuthority model carrier) = true /\
      runtimeCostReferencePresent (carrierRuntimeAuthority model carrier) = true /\
      runtimeCostReferenceKnown (carrierRuntimeAuthority model carrier) = true.
Proof.
  intros model use Hcert Hrequired.
  destruct (certified_required_runtime_use_has_exact_carrier
    model use Hcert Hrequired) as [carrier [Hexact Hknown]].
  assert (Hauthority :
    verifyRuntimeAuthority (carrierRuntimeAuthority model carrier) = GateAccepted).
  { unfold ExactCarrierBinding in Hexact. tauto. }
  pose proof
    (successful_runtime_authority_is_complete
      (carrierRuntimeAuthority model carrier) Hauthority)
    as Hcomplete.
  exists carrier.
  split.
  - exact Hexact.
  - exact Hcomplete.
Qed.

Theorem certified_covered_use_has_exact_selected_site_evidence_and_cost :
  forall model use carrier,
    RuntimeCarrierCertified model ->
    ExactCarrierBinding model use carrier ->
    runtimeEvidenceSelected
      (graphRuntimeEnvironment (carrierGraph model))
      (carrierUseEvidence model use) = true /\
    runtimeEvidenceRevision
      (graphRuntimeEnvironment (carrierGraph model))
      (carrierUseEvidence model use) =
        Some (carrierUseObligation model use) /\
    runtimeEvidenceDeclaresCost
      (graphRuntimeEnvironment (carrierGraph model))
      (carrierUseEvidence model use)
      (carrierUseCost model use) = true.
Proof.
  intros model use carrier Hcert Hexact.
  destruct Hcert as [Hgraph Hbound Hphantom Huses Htransfers].
  assert (Hrevision :
    runtimeSiteRevision
      (graphRuntimeSite (carrierGraph model) (carrierUseSite model use)) =
      carrierUseObligation model use).
  { unfold ExactCarrierBinding in Hexact. tauto. }
  assert (Hevidence :
    runtimeSiteEvidence
      (graphRuntimeSite (carrierGraph model) (carrierUseSite model use)) =
      carrierUseEvidence model use).
  { unfold ExactCarrierBinding in Hexact. tauto. }
  assert (Hcost :
    runtimeSiteCost
      (graphRuntimeSite (carrierGraph model) (carrierUseSite model use)) =
      carrierUseCost model use).
  { unfold ExactCarrierBinding in Hexact. tauto. }
  pose proof
    (graph_site_uses_selected_runtime_evidence
      (carrierGraph model) (carrierUseSite model use) Hgraph)
    as Hselected.
  pose proof
    (graph_site_preserves_runtime_revision
      (carrierGraph model) (carrierUseSite model use) Hgraph)
    as HsiteRevision.
  pose proof
    (graph_site_uses_exact_declared_runtime_cost
      (carrierGraph model) (carrierUseSite model use) Hgraph)
    as HdeclaredCost.
  rewrite Hevidence in Hselected.
  rewrite Hevidence in HsiteRevision.
  rewrite Hrevision in HsiteRevision.
  rewrite Hevidence in HdeclaredCost.
  rewrite Hcost in HdeclaredCost.
  repeat split; assumption.
Qed.

Theorem certified_covered_use_has_exact_claim_charge_lineage :
  forall model use carrier,
    RuntimeCarrierCertified model ->
    ExactCarrierBinding model use carrier ->
    exists contribution charge,
      ClaimContribution
        (carrierGraph model)
        (carrierClaim model carrier)
        contribution /\
      ClaimCharge
        (carrierGraph model)
        (carrierClaim model carrier)
        charge.
Proof.
  intros model use carrier Hcert Hexact.
  assert (Hclaim :
    graphClaimAtSite
      (carrierGraph model)
      (carrierClaim model carrier)
      (carrierUseSite model use)).
  { unfold ExactCarrierBinding in Hexact. tauto. }
  exists (graphSiteContribution (carrierGraph model) (carrierUseSite model use)).
  exists (graphContributionCharge
    (carrierGraph model)
    (graphSiteContribution (carrierGraph model) (carrierUseSite model use))).
  split.
  - exists (carrierUseSite model use).
    split; [exact Hclaim | reflexivity].
  - exists (graphSiteContribution (carrierGraph model) (carrierUseSite model use)).
    split.
    + exists (carrierUseSite model use).
      split; [exact Hclaim | reflexivity].
    + unfold ContributionInCharge.
      reflexivity.
Qed.

Theorem certified_potentially_violating_use_is_accounted :
  forall model use,
    RuntimeCarrierCertified model ->
    carrierPotentiallyViolatingUse model use = true ->
    carrierUseDisposition model use = CarrierUseStaticallySafe \/
    (exists carrier,
      carrierUseDisposition model use = CarrierUseCovered carrier /\
      ExactCarrierBinding model use carrier) \/
    (exists boundary,
      carrierUseDisposition model use = CarrierUseExplicitBoundary boundary /\
      boundary <> 0).
Proof.
  intros model use Hcert Hviolating.
  destruct Hcert as [Hgraph Hbound Hphantom Huses Htransfers].
  specialize (Huses use Hviolating).
  unfold CarrierUseAccounted in Huses.
  destruct (carrierUseDisposition model use) as [|carrier|boundary] eqn:Hdisp.
  - left. reflexivity.
  - right. left. exists carrier. split; [reflexivity | exact Huses].
  - right. right. exists boundary. split; [reflexivity | exact Huses].
Qed.

Theorem certified_active_transfer_cannot_silently_drop_carrier :
  forall model transition,
    RuntimeCarrierCertified model ->
    carrierTransitionActive model transition = true ->
    CarrierTransitionAccounted model transition.
Proof.
  intros model transition Hcert Hactive.
  destruct Hcert as [Hgraph Hbound Hphantom Huses Htransfers].
  exact (Htransfers transition Hactive).
Qed.

Theorem missing_required_carrier_binding_cannot_certify :
  forall model use,
    carrierRequiredUse model use = true ->
    carrierBinding model use = None ->
    ~ RuntimeCarrierCertified model.
Proof.
  intros model use Hrequired Hmissing Hcert.
  destruct Hcert as [Hgraph Hbound Hphantom Huses Htransfers].
  destruct (Hbound use Hrequired) as [carrier Hexact].
  destruct Hexact as [Hbinding _].
  rewrite Hmissing in Hbinding.
  discriminate.
Qed.

Theorem phantom_carrier_binding_cannot_certify :
  forall model use carrier,
    carrierBinding model use = Some carrier ->
    carrierKnown model carrier = false ->
    ~ RuntimeCarrierCertified model.
Proof.
  intros model use carrier Hbinding Hunknown Hcert.
  destruct Hcert as [Hgraph Hbound Hphantom Huses Htransfers].
  destruct (Hphantom use carrier Hbinding) as [Hrequired Hknown].
  rewrite Hunknown in Hknown.
  discriminate.
Qed.

Theorem incomplete_runtime_mechanism_cannot_certify_required_use :
  forall model use carrier,
    carrierRequiredUse model use = true ->
    carrierBinding model use = Some carrier ->
    runtimeMechanismComplete (carrierRuntimeAuthority model carrier) = false ->
    ~ RuntimeCarrierCertified model.
Proof.
  intros model use carrier Hrequired Hbinding Hincomplete Hcert.
  destruct (certified_required_runtime_use_has_complete_runtime_authority
    model use Hcert Hrequired)
    as [boundCarrier [Hexact
      [Hpresent [Hcomplete [Hresidue [Hcost [HknownCost]]]]]]].
  destruct Hexact as [HexactBinding _].
  rewrite Hbinding in HexactBinding.
  inversion HexactBinding; subst boundCarrier.
  rewrite Hincomplete in Hcomplete.
  discriminate.
Qed.
