From Phil.Core Require Import SystemsEvidencePreservation.

Inductive EvidenceErasureDecision : Type :=
| EvidenceErasureAcceptedDecision
| EvidenceErasureAssuranceUseDecision
| EvidenceErasureSourceSubjectDecision
| EvidenceErasureDischargeSubjectDecision
| EvidenceErasureRepresentationDecision
| EvidenceErasureLastUseDecision
| EvidenceErasureConsumerClosureBasisDecision
| EvidenceErasureSuccessorRevisionDecision
| EvidenceErasureRuntimeResidueRevisionDecision
| EvidenceErasureCostRevisionDecision
| EvidenceErasureLaterConsumersDecision.

Definition decideEvidenceErasureByFacts
  (assuranceUseAccepted sourceSubjectExact dischargeSubjectExact
   representationPresent lastUsePresent consumerClosureBasisPresent
   successorRevisionWellFormed runtimeResidueRevisionWellFormed
   costRevisionWellFormed laterConsumersClosed : bool)
  : EvidenceErasureDecision :=
  if assuranceUseAccepted then
    if sourceSubjectExact then
      if dischargeSubjectExact then
        if representationPresent then
          if lastUsePresent then
            if consumerClosureBasisPresent then
              if successorRevisionWellFormed then
                if runtimeResidueRevisionWellFormed then
                  if costRevisionWellFormed then
                    if laterConsumersClosed
                    then EvidenceErasureAcceptedDecision
                    else EvidenceErasureLaterConsumersDecision
                  else EvidenceErasureCostRevisionDecision
                else EvidenceErasureRuntimeResidueRevisionDecision
              else EvidenceErasureSuccessorRevisionDecision
            else EvidenceErasureConsumerClosureBasisDecision
          else EvidenceErasureLastUseDecision
        else EvidenceErasureRepresentationDecision
      else EvidenceErasureDischargeSubjectDecision
    else EvidenceErasureSourceSubjectDecision
  else EvidenceErasureAssuranceUseDecision.

Theorem evidence_erasure_decision_exact :
  forall assuranceUseAccepted sourceSubjectExact dischargeSubjectExact
         representationPresent lastUsePresent consumerClosureBasisPresent
         successorRevisionWellFormed runtimeResidueRevisionWellFormed
         costRevisionWellFormed laterConsumersClosed,
    decideEvidenceErasureByFacts
      assuranceUseAccepted sourceSubjectExact dischargeSubjectExact
      representationPresent lastUsePresent consumerClosureBasisPresent
      successorRevisionWellFormed runtimeResidueRevisionWellFormed
      costRevisionWellFormed laterConsumersClosed =
      EvidenceErasureAcceptedDecision <->
    assuranceUseAccepted = true /\
    sourceSubjectExact = true /\
    dischargeSubjectExact = true /\
    representationPresent = true /\
    lastUsePresent = true /\
    consumerClosureBasisPresent = true /\
    successorRevisionWellFormed = true /\
    runtimeResidueRevisionWellFormed = true /\
    costRevisionWellFormed = true /\
    laterConsumersClosed = true.
Proof.
  intros assuranceUseAccepted sourceSubjectExact dischargeSubjectExact
    representationPresent lastUsePresent consumerClosureBasisPresent
    successorRevisionWellFormed runtimeResidueRevisionWellFormed
    costRevisionWellFormed laterConsumersClosed.
  unfold decideEvidenceErasureByFacts.
  destruct assuranceUseAccepted;
  destruct sourceSubjectExact;
  destruct dischargeSubjectExact;
  destruct representationPresent;
  destruct lastUsePresent;
  destruct consumerClosureBasisPresent;
  destruct successorRevisionWellFormed;
  destruct runtimeResidueRevisionWellFormed;
  destruct costRevisionWellFormed;
  destruct laterConsumersClosed;
  simpl; intuition discriminate.
Qed.

Theorem evidence_erasure_decision_corresponds_certified_relation :
  forall context revision selected facts laterConsumers
         assuranceUseAccepted sourceSubjectExact dischargeSubjectExact
         representationPresent lastUsePresent consumerClosureBasisPresent
         successorRevisionWellFormed runtimeResidueRevisionWellFormed
         costRevisionWellFormed laterConsumersClosed,
    (assuranceUseAccepted = true <->
      ErasureUseVerified context revision selected) ->
    (sourceSubjectExact = true <->
      erasureSourceFactBindsExactSubject facts = true) ->
    (dischargeSubjectExact = true <->
      erasureDischargeEvidenceBindsExactSubject facts = true) ->
    (representationPresent = true <->
      erasureRepresentationRevision facts <> 0) ->
    (lastUsePresent = true <->
      erasureLastSemanticUse facts <> 0) ->
    (consumerClosureBasisPresent = true <->
      erasureNoLaterConsumerBasisRevision facts <> 0) ->
    (successorRevisionWellFormed = true <->
      OptionalRevisionWellFormed (erasureSuccessorInvariantRevision facts)) ->
    (runtimeResidueRevisionWellFormed = true <->
      OptionalRevisionWellFormed (erasureRuntimeResidueChangeRevision facts)) ->
    (costRevisionWellFormed = true <->
      OptionalRevisionWellFormed (erasureCostChangeRevision facts)) ->
    (laterConsumersClosed = true <->
      forall consumer basis,
        laterConsumers consumer = Some basis ->
        consumer <> erasureLastSemanticUse facts /\
        LaterConsumerSafe facts basis) ->
    decideEvidenceErasureByFacts
      assuranceUseAccepted sourceSubjectExact dischargeSubjectExact
      representationPresent lastUsePresent consumerClosureBasisPresent
      successorRevisionWellFormed runtimeResidueRevisionWellFormed
      costRevisionWellFormed laterConsumersClosed =
      EvidenceErasureAcceptedDecision <->
    EvidenceErasurePreserved
      context revision selected facts laterConsumers.
Proof.
  intros context revision selected facts laterConsumers
    assuranceUseAccepted sourceSubjectExact dischargeSubjectExact
    representationPresent lastUsePresent consumerClosureBasisPresent
    successorRevisionWellFormed runtimeResidueRevisionWellFormed
    costRevisionWellFormed laterConsumersClosed
    Huse Hsource Hdischarge Hrepresentation Hlast Hclosure
    Hsuccessor Hruntime Hcost Hconsumers.
  rewrite evidence_erasure_decision_exact.
  split.
  - intros [HuseB [HsourceB [HdischargeB [HrepresentationB [HlastB
      [HclosureB [HsuccessorB [HruntimeB [HcostB HconsumersB]]]]]]]]].
    constructor.
    + apply (proj1 Huse). exact HuseB.
    + apply (proj1 Hsource). exact HsourceB.
    + apply (proj1 Hdischarge). exact HdischargeB.
    + apply (proj1 Hrepresentation). exact HrepresentationB.
    + apply (proj1 Hlast). exact HlastB.
    + apply (proj1 Hclosure). exact HclosureB.
    + apply (proj1 Hsuccessor). exact HsuccessorB.
    + apply (proj1 Hruntime). exact HruntimeB.
    + apply (proj1 Hcost). exact HcostB.
    + apply (proj1 Hconsumers). exact HconsumersB.
  - intros Hpreserved.
    destruct Hpreserved as
      [HuseP HsourceP HdischargeP HrepresentationP HlastP HclosureP
       HsuccessorP HruntimeP HcostP HconsumersP].
    repeat split.
    + apply (proj2 Huse). exact HuseP.
    + apply (proj2 Hsource). exact HsourceP.
    + apply (proj2 Hdischarge). exact HdischargeP.
    + apply (proj2 Hrepresentation). exact HrepresentationP.
    + apply (proj2 Hlast). exact HlastP.
    + apply (proj2 Hclosure). exact HclosureP.
    + apply (proj2 Hsuccessor). exact HsuccessorP.
    + apply (proj2 Hruntime). exact HruntimeP.
    + apply (proj2 Hcost). exact HcostP.
    + apply (proj2 Hconsumers). exact HconsumersP.
Qed.

Inductive AssumptionDependencyDecision : Type :=
| AssumptionDependencyAcceptedDecision
| AssumptionRegistryDecision
| AssumptionAuthorityDecision
| AssumptionValidityScopeDecision
| AssumptionForwardDecision
| AssumptionForwardScopeDecision
| AssumptionReverseDecision.

Definition decideAssumptionDependencyByFacts
  (registryExact authorityAccepted validityScopesPresent forwardExact
   forwardScopesExact reverseExact : bool)
  : AssumptionDependencyDecision :=
  if registryExact then
    if authorityAccepted then
      if validityScopesPresent then
        if forwardExact then
          if forwardScopesExact then
            if reverseExact
            then AssumptionDependencyAcceptedDecision
            else AssumptionReverseDecision
          else AssumptionForwardScopeDecision
        else AssumptionForwardDecision
      else AssumptionValidityScopeDecision
    else AssumptionAuthorityDecision
  else AssumptionRegistryDecision.

Theorem assumption_dependency_decision_exact :
  forall registryExact authorityAccepted validityScopesPresent forwardExact
         forwardScopesExact reverseExact,
    decideAssumptionDependencyByFacts
      registryExact authorityAccepted validityScopesPresent forwardExact
      forwardScopesExact reverseExact = AssumptionDependencyAcceptedDecision <->
    registryExact = true /\
    authorityAccepted = true /\
    validityScopesPresent = true /\
    forwardExact = true /\
    forwardScopesExact = true /\
    reverseExact = true.
Proof.
  intros registryExact authorityAccepted validityScopesPresent forwardExact
    forwardScopesExact reverseExact.
  unfold decideAssumptionDependencyByFacts.
  destruct registryExact;
  destruct authorityAccepted;
  destruct validityScopesPresent;
  destruct forwardExact;
  destruct forwardScopesExact;
  destruct reverseExact;
  simpl; intuition discriminate.
Qed.

Theorem assumption_dependency_decision_corresponds_certified_relation :
  forall required registry forward reverse
         registryExact authorityAccepted validityScopesPresent forwardExact
         forwardScopesExact reverseExact,
    (registryExact = true <->
      forall assumption,
        (exists consumer, required consumer assumption) <->
        (exists binding, registry assumption = Some binding)) ->
    (authorityAccepted = true <->
      forall assumption binding,
        registry assumption = Some binding ->
        verifyAssumptionAuthority (systemsAssumptionAuthority binding) =
          GateAccepted) ->
    (validityScopesPresent = true <->
      forall assumption binding,
        registry assumption = Some binding ->
        systemsAssumptionValidityScopeRevision binding <> 0) ->
    (forwardExact = true <->
      forall consumer assumption,
        required consumer assumption <->
        (exists scope, forward consumer assumption = Some scope)) ->
    (forwardScopesExact = true <->
      forall consumer assumption scope,
        forward consumer assumption = Some scope ->
        exists binding,
          registry assumption = Some binding /\
          scope = systemsAssumptionValidityScopeRevision binding) ->
    (reverseExact = true <->
      forall consumer assumption,
        reverse assumption consumer = true <-> required consumer assumption) ->
    decideAssumptionDependencyByFacts
      registryExact authorityAccepted validityScopesPresent forwardExact
      forwardScopesExact reverseExact = AssumptionDependencyAcceptedDecision <->
    SystemsAssumptionDependenciesPreserved required registry forward reverse.
Proof.
  intros required registry forward reverse
    registryExact authorityAccepted validityScopesPresent forwardExact
    forwardScopesExact reverseExact
    Hregistry Hauthority Hscope Hforward HforwardScope Hreverse.
  rewrite assumption_dependency_decision_exact.
  split.
  - intros [HregistryB [HauthorityB [HscopeB
      [HforwardB [HforwardScopeB HreverseB]]]]].
    constructor.
    + apply (proj1 Hregistry). exact HregistryB.
    + apply (proj1 Hauthority). exact HauthorityB.
    + apply (proj1 Hscope). exact HscopeB.
    + apply (proj1 Hforward). exact HforwardB.
    + apply (proj1 HforwardScope). exact HforwardScopeB.
    + apply (proj1 Hreverse). exact HreverseB.
  - intros Hpreserved.
    destruct Hpreserved as
      [HregistryP HauthorityP HscopeP HforwardP HforwardScopeP HreverseP].
    repeat split.
    + apply (proj2 Hregistry). exact HregistryP.
    + apply (proj2 Hauthority). exact HauthorityP.
    + apply (proj2 Hscope). exact HscopeP.
    + apply (proj2 Hforward). exact HforwardP.
    + apply (proj2 HforwardScope). exact HforwardScopeP.
    + apply (proj2 Hreverse). exact HreverseP.
Qed.

Inductive SystemsEvidenceDecision : Type :=
| SystemsEvidenceAcceptedDecision
| SystemsEvidenceSubjectTransferDecision
| SystemsEvidenceErasureDecision
| SystemsEvidenceAssumptionDecision.

Definition decideSystemsEvidenceByFacts
  (subjectTransferAccepted erasureAccepted assumptionsAccepted : bool)
  : SystemsEvidenceDecision :=
  if subjectTransferAccepted then
    if erasureAccepted then
      if assumptionsAccepted
      then SystemsEvidenceAcceptedDecision
      else SystemsEvidenceAssumptionDecision
    else SystemsEvidenceErasureDecision
  else SystemsEvidenceSubjectTransferDecision.

Theorem systems_evidence_decision_exact :
  forall subjectTransferAccepted erasureAccepted assumptionsAccepted,
    decideSystemsEvidenceByFacts
      subjectTransferAccepted erasureAccepted assumptionsAccepted =
      SystemsEvidenceAcceptedDecision <->
    subjectTransferAccepted = true /\
    erasureAccepted = true /\
    assumptionsAccepted = true.
Proof.
  intros subjectTransferAccepted erasureAccepted assumptionsAccepted.
  unfold decideSystemsEvidenceByFacts.
  destruct subjectTransferAccepted;
  destruct erasureAccepted;
  destruct assumptionsAccepted;
  simpl; intuition discriminate.
Qed.

Theorem systems_evidence_decision_corresponds_certified_relation :
  forall update evidence transfer resultEvidence
         context erasureRevision selectedErasureEvidence
         erasureFacts laterConsumers required registry forward reverse
         subjectTransferAccepted erasureAccepted assumptionsAccepted,
    (subjectTransferAccepted = true <->
      CheckedDataSubjectUpdate
        update evidence (Some (boundaryDataTransport transfer)) resultEvidence /\
      BoundarySubjectTransferAccepted evidence transfer) ->
    (erasureAccepted = true <->
      EvidenceErasurePreserved
        context erasureRevision selectedErasureEvidence
        erasureFacts laterConsumers) ->
    (assumptionsAccepted = true <->
      SystemsAssumptionDependenciesPreserved
        required registry forward reverse) ->
    decideSystemsEvidenceByFacts
      subjectTransferAccepted erasureAccepted assumptionsAccepted =
      SystemsEvidenceAcceptedDecision <->
    SystemsEvidencePreserved
      update evidence transfer resultEvidence
      context erasureRevision selectedErasureEvidence
      erasureFacts laterConsumers required registry forward reverse.
Proof.
  intros update evidence transfer resultEvidence
    context erasureRevision selectedErasureEvidence
    erasureFacts laterConsumers required registry forward reverse
    subjectTransferAccepted erasureAccepted assumptionsAccepted
    Hsubject Herasure Hassumptions.
  rewrite systems_evidence_decision_exact.
  split.
  - intros [HsubjectB [HerasureB HassumptionsB]].
    apply (proj1 Hsubject) in HsubjectB.
    destruct HsubjectB as [Hupdate Htransfer].
    constructor.
    + exact Hupdate.
    + exact Htransfer.
    + apply (proj1 Herasure). exact HerasureB.
    + apply (proj1 Hassumptions). exact HassumptionsB.
  - intros Hpreserved.
    destruct Hpreserved as [Hupdate Htransfer HerasureP HassumptionsP].
    repeat split.
    + apply (proj2 Hsubject). split; assumption.
    + apply (proj2 Herasure). exact HerasureP.
    + apply (proj2 Hassumptions). exact HassumptionsP.
Qed.
