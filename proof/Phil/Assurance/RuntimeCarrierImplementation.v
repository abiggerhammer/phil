From Stdlib Require Import Bool.Bool.

From Phil.Assurance Require Import EvidenceUse RuntimeCarrier.
From Phil.Core Require Import SystemsRuntimeGraph.
From Phil.Systems Require Import Runtime.

(*
  PHIL-ASSURE-CARRIER-001 — representation-neutral executable decision
  kernels for the Certified Runtime Carrier relation.

  Concrete Text/Map/Set/list representation, enumeration of retained or
  potentially violating uses, runtime-site lookup, process-realization lookup,
  failure-fact lookup, and diagnostic payload construction stay native.
  Production reflects the exact semantic facts established by those checks into
  Booleans; the extracted kernel owns final acceptance for the Certified
  retained-use binding and carrier-transition predicates.
*)

Definition decideExactCarrierBindingByFacts
  (bindingExact requiredUse carrierKnown dispositionCovered obligationExact
   siteRevisionExact siteEvidenceExact siteCostExact establishedAtSite
   claimAtSite processExact executionCovered runtimeAuthorityAccepted : bool)
  : bool :=
  andb bindingExact
    (andb requiredUse
      (andb carrierKnown
        (andb dispositionCovered
          (andb obligationExact
            (andb siteRevisionExact
              (andb siteEvidenceExact
                (andb siteCostExact
                  (andb establishedAtSite
                    (andb claimAtSite
                      (andb processExact
                        (andb executionCovered runtimeAuthorityAccepted))))))))))).

Theorem exact_carrier_binding_decision_accept_iff_certified :
  forall model use carrier
         bindingExact requiredUse carrierKnown0 dispositionCovered obligationExact
         siteRevisionExact siteEvidenceExact siteCostExact establishedAtSite
         claimAtSite processExact executionCovered runtimeAuthorityAccepted,
    (bindingExact = true <-> carrierBinding model use = Some carrier) ->
    (requiredUse = true <-> carrierRequiredUse model use = true) ->
    (carrierKnown0 = true <-> carrierKnown model carrier = true) ->
    (dispositionCovered = true <->
      carrierUseDisposition model use = CarrierUseCovered carrier) ->
    (obligationExact = true <->
      carrierUseObligation model use = carrierObligation model carrier) ->
    (siteRevisionExact = true <->
      runtimeSiteRevision
        (graphRuntimeSite (carrierGraph model) (carrierUseSite model use)) =
      carrierUseObligation model use) ->
    (siteEvidenceExact = true <->
      runtimeSiteEvidence
        (graphRuntimeSite (carrierGraph model) (carrierUseSite model use)) =
      carrierUseEvidence model use) ->
    (siteCostExact = true <->
      runtimeSiteCost
        (graphRuntimeSite (carrierGraph model) (carrierUseSite model use)) =
      carrierUseCost model use) ->
    (establishedAtSite = true <->
      carrierEstablishedAt model carrier (carrierUseSite model use) = true) ->
    (claimAtSite = true <->
      graphClaimAtSite
        (carrierGraph model)
        (carrierClaim model carrier)
        (carrierUseSite model use)) ->
    (processExact = true <->
      carrierUseProcess model use = carrierProcess model carrier) ->
    (executionCovered = true <->
      carrierExecutionCovered model carrier (carrierUseExecution model use) = true) ->
    (runtimeAuthorityAccepted = true <->
      verifyRuntimeAuthority (carrierRuntimeAuthority model carrier) = GateAccepted) ->
    decideExactCarrierBindingByFacts
      bindingExact requiredUse carrierKnown0 dispositionCovered obligationExact
      siteRevisionExact siteEvidenceExact siteCostExact establishedAtSite
      claimAtSite processExact executionCovered runtimeAuthorityAccepted = true <->
    ExactCarrierBinding model use carrier.
Proof.
  intros model use carrier
    bindingExact requiredUse carrierKnown0 dispositionCovered obligationExact
    siteRevisionExact siteEvidenceExact siteCostExact establishedAtSite
    claimAtSite0 processExact executionCovered runtimeAuthorityAccepted
    Hbinding Hrequired Hknown Hdisposition Hobligation Hrevision Hevidence Hcost
    Hestablished Hclaim Hprocess Hexecution Hruntime.
  unfold decideExactCarrierBindingByFacts, ExactCarrierBinding.
  repeat rewrite andb_true_iff.
  rewrite Hbinding, Hrequired, Hknown, Hdisposition, Hobligation,
          Hrevision, Hevidence, Hcost, Hestablished, Hclaim,
          Hprocess, Hexecution, Hruntime.
  reflexivity.
Qed.

Definition decideCoveredCarrierUseByFacts (exactBinding : bool) : bool :=
  exactBinding.

Theorem covered_carrier_use_decision_accept_iff_certified :
  forall model use carrier exactBinding,
    carrierUseDisposition model use = CarrierUseCovered carrier ->
    (exactBinding = true <-> ExactCarrierBinding model use carrier) ->
    decideCoveredCarrierUseByFacts exactBinding = true <->
    CarrierUseAccounted model use.
Proof.
  intros model use carrier exactBinding Hdisposition Hbinding.
  unfold decideCoveredCarrierUseByFacts, CarrierUseAccounted.
  rewrite Hdisposition.
  exact Hbinding.
Qed.

Definition decideExplicitBoundaryCarrierUseByFacts
  (boundaryNonzero : bool) : bool :=
  boundaryNonzero.

Theorem explicit_boundary_carrier_use_decision_accept_iff_certified :
  forall model use boundary boundaryNonzero,
    carrierUseDisposition model use = CarrierUseExplicitBoundary boundary ->
    (boundaryNonzero = true <-> boundary <> 0) ->
    decideExplicitBoundaryCarrierUseByFacts boundaryNonzero = true <->
    CarrierUseAccounted model use.
Proof.
  intros model use boundary boundaryNonzero Hdisposition Hboundary.
  unfold decideExplicitBoundaryCarrierUseByFacts, CarrierUseAccounted.
  rewrite Hdisposition.
  exact Hboundary.
Qed.

Definition decidePreservedCarrierTransitionByFacts
  (carrierKnown obligationExact processExact fromCovered toCovered : bool)
  : bool :=
  andb carrierKnown
    (andb obligationExact
      (andb processExact
        (andb fromCovered toCovered))).

Theorem preserved_carrier_transition_decision_accept_iff_certified :
  forall model transition carrier
         carrierKnown0 obligationExact processExact fromCovered toCovered,
    carrierTransitionDisposition model transition = CarrierPreserved carrier ->
    (carrierKnown0 = true <-> carrierKnown model carrier = true) ->
    (obligationExact = true <->
      carrierTransitionObligation model transition = carrierObligation model carrier) ->
    (processExact = true <->
      carrierTransitionProcess model transition = carrierProcess model carrier) ->
    (fromCovered = true <->
      carrierExecutionCovered model carrier
        (carrierTransitionFrom model transition) = true) ->
    (toCovered = true <->
      carrierExecutionCovered model carrier
        (carrierTransitionTo model transition) = true) ->
    decidePreservedCarrierTransitionByFacts
      carrierKnown0 obligationExact processExact fromCovered toCovered = true <->
    CarrierTransitionAccounted model transition.
Proof.
  intros model transition carrier
    carrierKnown0 obligationExact processExact fromCovered toCovered
    Hdisposition Hknown Hobligation Hprocess Hfrom Hto.
  unfold decidePreservedCarrierTransitionByFacts, CarrierTransitionAccounted.
  rewrite Hdisposition.
  repeat rewrite andb_true_iff.
  rewrite Hknown, Hobligation, Hprocess, Hfrom, Hto.
  reflexivity.
Qed.

Definition decideReplacedCarrierTransitionByFacts
  (priorKnown nextKnown obligationPriorExact obligationNextExact
   processPriorExact processNextExact fromCovered toCovered : bool) : bool :=
  andb priorKnown
    (andb nextKnown
      (andb obligationPriorExact
        (andb obligationNextExact
          (andb processPriorExact
            (andb processNextExact
              (andb fromCovered toCovered)))))).

Theorem replaced_carrier_transition_decision_accept_iff_certified :
  forall model transition prior next
         priorKnown nextKnown obligationPriorExact obligationNextExact
         processPriorExact processNextExact fromCovered toCovered,
    carrierTransitionDisposition model transition = CarrierReplaced prior next ->
    (priorKnown = true <-> carrierKnown model prior = true) ->
    (nextKnown = true <-> carrierKnown model next = true) ->
    (obligationPriorExact = true <->
      carrierTransitionObligation model transition = carrierObligation model prior) ->
    (obligationNextExact = true <->
      carrierTransitionObligation model transition = carrierObligation model next) ->
    (processPriorExact = true <->
      carrierTransitionProcess model transition = carrierProcess model prior) ->
    (processNextExact = true <->
      carrierTransitionProcess model transition = carrierProcess model next) ->
    (fromCovered = true <->
      carrierExecutionCovered model prior
        (carrierTransitionFrom model transition) = true) ->
    (toCovered = true <->
      carrierExecutionCovered model next
        (carrierTransitionTo model transition) = true) ->
    decideReplacedCarrierTransitionByFacts
      priorKnown nextKnown obligationPriorExact obligationNextExact
      processPriorExact processNextExact fromCovered toCovered = true <->
    CarrierTransitionAccounted model transition.
Proof.
  intros model transition prior next
    priorKnown nextKnown obligationPriorExact obligationNextExact
    processPriorExact processNextExact fromCovered toCovered
    Hdisposition Hprior Hnext HobligationPrior HobligationNext
    HprocessPrior HprocessNext Hfrom Hto.
  unfold decideReplacedCarrierTransitionByFacts, CarrierTransitionAccounted.
  rewrite Hdisposition.
  repeat rewrite andb_true_iff.
  rewrite Hprior, Hnext, HobligationPrior, HobligationNext,
          HprocessPrior, HprocessNext, Hfrom, Hto.
  reflexivity.
Qed.

Definition decideClosedCarrierTransitionByFacts
  (carrierKnown obligationExact processExact fromCovered destinationNotRuntimeBound
   : bool) : bool :=
  andb carrierKnown
    (andb obligationExact
      (andb processExact
        (andb fromCovered destinationNotRuntimeBound))).

Theorem discharged_carrier_transition_decision_accept_iff_certified :
  forall model transition carrier
         carrierKnown0 obligationExact processExact fromCovered destinationNotRuntimeBound,
    carrierTransitionDisposition model transition = CarrierDischarged carrier ->
    (carrierKnown0 = true <-> carrierKnown model carrier = true) ->
    (obligationExact = true <->
      carrierTransitionObligation model transition = carrierObligation model carrier) ->
    (processExact = true <->
      carrierTransitionProcess model transition = carrierProcess model carrier) ->
    (fromCovered = true <->
      carrierExecutionCovered model carrier
        (carrierTransitionFrom model transition) = true) ->
    (destinationNotRuntimeBound = true <->
      carrierTransitionDestinationRuntimeBound model transition = false) ->
    decideClosedCarrierTransitionByFacts
      carrierKnown0 obligationExact processExact fromCovered destinationNotRuntimeBound = true <->
    CarrierTransitionAccounted model transition.
Proof.
  intros model transition carrier
    carrierKnown0 obligationExact processExact fromCovered destinationNotRuntimeBound
    Hdisposition Hknown Hobligation Hprocess Hfrom Hdestination.
  unfold decideClosedCarrierTransitionByFacts, CarrierTransitionAccounted.
  rewrite Hdisposition.
  repeat rewrite andb_true_iff.
  rewrite Hknown, Hobligation, Hprocess, Hfrom, Hdestination.
  reflexivity.
Qed.

Theorem ended_carrier_validity_transition_decision_accept_iff_certified :
  forall model transition carrier
         carrierKnown0 obligationExact processExact fromCovered destinationNotRuntimeBound,
    carrierTransitionDisposition model transition = CarrierValidityEnded carrier ->
    (carrierKnown0 = true <-> carrierKnown model carrier = true) ->
    (obligationExact = true <->
      carrierTransitionObligation model transition = carrierObligation model carrier) ->
    (processExact = true <->
      carrierTransitionProcess model transition = carrierProcess model carrier) ->
    (fromCovered = true <->
      carrierExecutionCovered model carrier
        (carrierTransitionFrom model transition) = true) ->
    (destinationNotRuntimeBound = true <->
      carrierTransitionDestinationRuntimeBound model transition = false) ->
    decideClosedCarrierTransitionByFacts
      carrierKnown0 obligationExact processExact fromCovered destinationNotRuntimeBound = true <->
    CarrierTransitionAccounted model transition.
Proof.
  intros model transition carrier
    carrierKnown0 obligationExact processExact fromCovered destinationNotRuntimeBound
    Hdisposition Hknown Hobligation Hprocess Hfrom Hdestination.
  unfold decideClosedCarrierTransitionByFacts, CarrierTransitionAccounted.
  rewrite Hdisposition.
  repeat rewrite andb_true_iff.
  rewrite Hknown, Hobligation, Hprocess, Hfrom, Hdestination.
  reflexivity.
Qed.
