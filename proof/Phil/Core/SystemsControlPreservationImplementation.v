From Phil.Core Require Import SystemsControlPreservation.

Inductive BranchPreservationDecision : Type :=
| BranchPreservationAcceptedDecision
| BranchOutcomeDomainDecision
| BranchOwnerFateDomainDecision
| BranchOwnerFateRealizationDecision
| BranchControlClassDecision
| BranchTrackedOwnerDecision.

Definition decideBranchPreservationByFacts
  (outcomeDomainExact ownerFateDomainExact ownerFateRealizedExactlyOnce
   controlClassExact trackedValuesAreOwners : bool)
  : BranchPreservationDecision :=
  if outcomeDomainExact then
    if ownerFateDomainExact then
      if ownerFateRealizedExactlyOnce then
        if controlClassExact then
          if trackedValuesAreOwners
          then BranchPreservationAcceptedDecision
          else BranchTrackedOwnerDecision
        else BranchControlClassDecision
      else BranchOwnerFateRealizationDecision
    else BranchOwnerFateDomainDecision
  else BranchOutcomeDomainDecision.

Definition reflectedBranchPreservationFacts
  (outcomeDomainExact ownerFateDomainExact ownerFateRealizedExactlyOnce
   controlClassExact trackedValuesAreOwners : bool)
  : BranchPreservationFacts :=
  {| branchOutcomeDomainExact := outcomeDomainExact;
     branchOwnerFateDomainExact := ownerFateDomainExact;
     branchOwnerFateRealizedExactlyOnce := ownerFateRealizedExactlyOnce;
     branchControlClassExact := controlClassExact;
     branchTrackedValuesAreOwners := trackedValuesAreOwners |}.

Theorem reflected_branch_preservation_decision_exact :
  forall outcomeDomainExact ownerFateDomainExact ownerFateRealizedExactlyOnce
         controlClassExact trackedValuesAreOwners,
    decideBranchPreservationByFacts
      outcomeDomainExact ownerFateDomainExact ownerFateRealizedExactlyOnce
      controlClassExact trackedValuesAreOwners = BranchPreservationAcceptedDecision <->
    branchPreserved
      (reflectedBranchPreservationFacts
        outcomeDomainExact ownerFateDomainExact ownerFateRealizedExactlyOnce
        controlClassExact trackedValuesAreOwners).
Proof.
  intros outcomeDomainExact ownerFateDomainExact ownerFateRealizedExactlyOnce
    controlClassExact trackedValuesAreOwners.
  unfold decideBranchPreservationByFacts, branchPreserved,
    reflectedBranchPreservationFacts.
  destruct outcomeDomainExact;
  destruct ownerFateDomainExact;
  destruct ownerFateRealizedExactlyOnce;
  destruct controlClassExact;
  destruct trackedValuesAreOwners;
  simpl; intuition discriminate.
Qed.

Inductive StateProjectionDecision : Type :=
| StateProjectionAcceptedDecision
| StateProjectionKindDecision
| StateSlotDomainDecision
| StateRestrictedOwnerModeDecision
| StateFixedSubjectDecision
| StateRestrictedOwnerUniqueDecision
| StateLinearOwnersCoveredDecision
| StateScopedLoanEscapeDecision
| ClosureCaptureCarrierDecision
| ClosureCarrierSharingDecision.

Definition decideStateProjectionByFacts
  (projectionKindExact slotDomainExact restrictedOwnerModeExact fixedSubjectExact
   restrictedOwnerUnique linearOwnersCovered scopedLoansDoNotEscape
   restrictedCaptureHasOneCarrier restrictedCarriersAreUnshared : bool)
  : StateProjectionDecision :=
  if projectionKindExact then
    if slotDomainExact then
      if restrictedOwnerModeExact then
        if fixedSubjectExact then
          if restrictedOwnerUnique then
            if linearOwnersCovered then
              if scopedLoansDoNotEscape then
                if restrictedCaptureHasOneCarrier then
                  if restrictedCarriersAreUnshared
                  then StateProjectionAcceptedDecision
                  else ClosureCarrierSharingDecision
                else ClosureCaptureCarrierDecision
              else StateScopedLoanEscapeDecision
            else StateLinearOwnersCoveredDecision
          else StateRestrictedOwnerUniqueDecision
        else StateFixedSubjectDecision
      else StateRestrictedOwnerModeDecision
    else StateSlotDomainDecision
  else StateProjectionKindDecision.

Definition reflectedStateProjectionFacts
  (projectionKindExact slotDomainExact restrictedOwnerModeExact fixedSubjectExact
   restrictedOwnerUnique linearOwnersCovered scopedLoansDoNotEscape
   restrictedCaptureHasOneCarrier restrictedCarriersAreUnshared : bool)
  : StateProjectionFacts :=
  {| stateProjectionKindExact := projectionKindExact;
     stateSlotDomainExact := slotDomainExact;
     stateRestrictedOwnerModeExact := restrictedOwnerModeExact;
     stateFixedSubjectExact := fixedSubjectExact;
     stateRestrictedOwnerUnique := restrictedOwnerUnique;
     stateLinearOwnersCovered := linearOwnersCovered;
     stateScopedLoansDoNotEscape := scopedLoansDoNotEscape;
     closureRestrictedCaptureHasOneCarrier := restrictedCaptureHasOneCarrier;
     closureRestrictedCarriersAreUnshared := restrictedCarriersAreUnshared |}.

Theorem reflected_state_projection_decision_exact :
  forall projectionKindExact slotDomainExact restrictedOwnerModeExact fixedSubjectExact
         restrictedOwnerUnique linearOwnersCovered scopedLoansDoNotEscape
         restrictedCaptureHasOneCarrier restrictedCarriersAreUnshared,
    decideStateProjectionByFacts
      projectionKindExact slotDomainExact restrictedOwnerModeExact fixedSubjectExact
      restrictedOwnerUnique linearOwnersCovered scopedLoansDoNotEscape
      restrictedCaptureHasOneCarrier restrictedCarriersAreUnshared =
      StateProjectionAcceptedDecision <->
    stateProjectionPreserved
      (reflectedStateProjectionFacts
        projectionKindExact slotDomainExact restrictedOwnerModeExact fixedSubjectExact
        restrictedOwnerUnique linearOwnersCovered scopedLoansDoNotEscape
        restrictedCaptureHasOneCarrier restrictedCarriersAreUnshared).
Proof.
  intros projectionKindExact slotDomainExact restrictedOwnerModeExact fixedSubjectExact
    restrictedOwnerUnique linearOwnersCovered scopedLoansDoNotEscape
    restrictedCaptureHasOneCarrier restrictedCarriersAreUnshared.
  unfold decideStateProjectionByFacts, stateProjectionPreserved,
    reflectedStateProjectionFacts.
  destruct projectionKindExact;
  destruct slotDomainExact;
  destruct restrictedOwnerModeExact;
  destruct fixedSubjectExact;
  destruct restrictedOwnerUnique;
  destruct linearOwnersCovered;
  destruct scopedLoansDoNotEscape;
  destruct restrictedCaptureHasOneCarrier;
  destruct restrictedCarriersAreUnshared;
  simpl; intuition discriminate.
Qed.

Inductive ProtocolPreservationDecision : Type :=
| ProtocolPreservationAcceptedDecision
| ProtocolBasisDecision
| ProtocolTargetSiteDecision
| ProtocolTransportUseDecision
| ProtocolOutcomeDomainDecision
| ProtocolInstanceDecision
| ProtocolRoleDecision
| ProtocolSuccessorFreshDecision
| ProtocolPredecessorConsumedDecision
| ProtocolSuccessorProducedDecision
| ProtocolLineageDecision.

Definition decideProtocolPreservationByFacts
  (basisIsChecked targetSiteExact transportUseExact outcomeDomainExact instanceExact
   roleExact successorIsFresh predecessorConsumedOnce successorProducedOnce lineageAcyclic : bool)
  : ProtocolPreservationDecision :=
  if basisIsChecked then
    if targetSiteExact then
      if transportUseExact then
        if outcomeDomainExact then
          if instanceExact then
            if roleExact then
              if successorIsFresh then
                if predecessorConsumedOnce then
                  if successorProducedOnce then
                    if lineageAcyclic
                    then ProtocolPreservationAcceptedDecision
                    else ProtocolLineageDecision
                  else ProtocolSuccessorProducedDecision
                else ProtocolPredecessorConsumedDecision
              else ProtocolSuccessorFreshDecision
            else ProtocolRoleDecision
          else ProtocolInstanceDecision
        else ProtocolOutcomeDomainDecision
      else ProtocolTransportUseDecision
    else ProtocolTargetSiteDecision
  else ProtocolBasisDecision.

Definition reflectedProtocolPreservationFacts
  (basisIsChecked targetSiteExact transportUseExact outcomeDomainExact instanceExact
   roleExact successorIsFresh predecessorConsumedOnce successorProducedOnce lineageAcyclic : bool)
  : ProtocolPreservationFacts :=
  {| protocolBasisIsChecked := basisIsChecked;
     protocolTargetSiteExact := targetSiteExact;
     protocolTransportUseExact := transportUseExact;
     protocolOutcomeDomainExact := outcomeDomainExact;
     protocolInstanceExact := instanceExact;
     protocolRoleExact := roleExact;
     protocolSuccessorIsFresh := successorIsFresh;
     protocolPredecessorConsumedOnce := predecessorConsumedOnce;
     protocolSuccessorProducedOnce := successorProducedOnce;
     protocolLineageAcyclic := lineageAcyclic |}.

Theorem reflected_protocol_preservation_decision_exact :
  forall basisIsChecked targetSiteExact transportUseExact outcomeDomainExact instanceExact
         roleExact successorIsFresh predecessorConsumedOnce successorProducedOnce lineageAcyclic,
    decideProtocolPreservationByFacts
      basisIsChecked targetSiteExact transportUseExact outcomeDomainExact instanceExact
      roleExact successorIsFresh predecessorConsumedOnce successorProducedOnce lineageAcyclic =
      ProtocolPreservationAcceptedDecision <->
    protocolPreserved
      (reflectedProtocolPreservationFacts
        basisIsChecked targetSiteExact transportUseExact outcomeDomainExact instanceExact
        roleExact successorIsFresh predecessorConsumedOnce successorProducedOnce lineageAcyclic).
Proof.
  intros basisIsChecked targetSiteExact transportUseExact outcomeDomainExact instanceExact
    roleExact successorIsFresh predecessorConsumedOnce successorProducedOnce lineageAcyclic.
  unfold decideProtocolPreservationByFacts, protocolPreserved,
    reflectedProtocolPreservationFacts.
  destruct basisIsChecked;
  destruct targetSiteExact;
  destruct transportUseExact;
  destruct outcomeDomainExact;
  destruct instanceExact;
  destruct roleExact;
  destruct successorIsFresh;
  destruct predecessorConsumedOnce;
  destruct successorProducedOnce;
  destruct lineageAcyclic;
  simpl; intuition discriminate.
Qed.

Inductive BoundaryCommitDecision : Type :=
| BoundaryCommitAcceptedDecision
| BoundarySourceRuntimeFactDecision
| BoundaryTransportDecision
| BoundaryOwnerDecision
| BoundarySubjectDecision
| BoundaryLengthDecision
| BoundaryRuntimeKindDecision
| BoundaryRuntimeRevisionEvidenceDecision
| BoundaryProtocolTransitionDecision
| BoundaryCommitSuccessorDecision
| BoundaryFailureTerminalDecision
| BoundaryCompleteBeforeSuccessDecision.

Definition decideBoundaryCommitByFacts
  (sourceRuntimeFactExact transportExact ownerExact subjectExact lengthExact runtimeKindExact
   runtimeRevisionEvidenceExact protocolTransitionExact commitProducesSuccessor
   failureRemainsTerminal completeBeforeSuccess : bool)
  : BoundaryCommitDecision :=
  if sourceRuntimeFactExact then
    if transportExact then
      if ownerExact then
        if subjectExact then
          if lengthExact then
            if runtimeKindExact then
              if runtimeRevisionEvidenceExact then
                if protocolTransitionExact then
                  if commitProducesSuccessor then
                    if failureRemainsTerminal then
                      if completeBeforeSuccess
                      then BoundaryCommitAcceptedDecision
                      else BoundaryCompleteBeforeSuccessDecision
                    else BoundaryFailureTerminalDecision
                  else BoundaryCommitSuccessorDecision
                else BoundaryProtocolTransitionDecision
              else BoundaryRuntimeRevisionEvidenceDecision
            else BoundaryRuntimeKindDecision
          else BoundaryLengthDecision
        else BoundarySubjectDecision
      else BoundaryOwnerDecision
    else BoundaryTransportDecision
  else BoundarySourceRuntimeFactDecision.

Definition reflectedBoundaryCommitFacts
  (sourceRuntimeFactExact transportExact ownerExact subjectExact lengthExact runtimeKindExact
   runtimeRevisionEvidenceExact protocolTransitionExact commitProducesSuccessor
   failureRemainsTerminal completeBeforeSuccess : bool)
  : BoundaryCommitFacts :=
  {| boundarySourceRuntimeFactExact := sourceRuntimeFactExact;
     boundaryTransportExact := transportExact;
     boundaryOwnerExact := ownerExact;
     boundarySubjectExact := subjectExact;
     boundaryLengthExact := lengthExact;
     boundaryRuntimeKindExact := runtimeKindExact;
     boundaryRuntimeRevisionEvidenceExact := runtimeRevisionEvidenceExact;
     boundaryProtocolTransitionExact := protocolTransitionExact;
     boundaryCommitProducesSuccessor := commitProducesSuccessor;
     boundaryFailureRemainsTerminal := failureRemainsTerminal;
     boundaryCompleteBeforeSuccess := completeBeforeSuccess |}.

Theorem reflected_boundary_commit_decision_exact :
  forall sourceRuntimeFactExact transportExact ownerExact subjectExact lengthExact runtimeKindExact
         runtimeRevisionEvidenceExact protocolTransitionExact commitProducesSuccessor
         failureRemainsTerminal completeBeforeSuccess,
    decideBoundaryCommitByFacts
      sourceRuntimeFactExact transportExact ownerExact subjectExact lengthExact runtimeKindExact
      runtimeRevisionEvidenceExact protocolTransitionExact commitProducesSuccessor
      failureRemainsTerminal completeBeforeSuccess = BoundaryCommitAcceptedDecision <->
    boundaryCommitPreserved
      (reflectedBoundaryCommitFacts
        sourceRuntimeFactExact transportExact ownerExact subjectExact lengthExact runtimeKindExact
        runtimeRevisionEvidenceExact protocolTransitionExact commitProducesSuccessor
        failureRemainsTerminal completeBeforeSuccess).
Proof.
  intros sourceRuntimeFactExact transportExact ownerExact subjectExact lengthExact runtimeKindExact
    runtimeRevisionEvidenceExact protocolTransitionExact commitProducesSuccessor
    failureRemainsTerminal completeBeforeSuccess.
  unfold decideBoundaryCommitByFacts, boundaryCommitPreserved,
    reflectedBoundaryCommitFacts.
  destruct sourceRuntimeFactExact;
  destruct transportExact;
  destruct ownerExact;
  destruct subjectExact;
  destruct lengthExact;
  destruct runtimeKindExact;
  destruct runtimeRevisionEvidenceExact;
  destruct protocolTransitionExact;
  destruct commitProducesSuccessor;
  destruct failureRemainsTerminal;
  destruct completeBeforeSuccess;
  simpl; intuition discriminate.
Qed.

Inductive SystemsControlDecision : Type :=
| SystemsControlAcceptedDecision
| SystemsControlBranchDecision
| SystemsControlStateDecision
| SystemsControlProtocolDecision
| SystemsControlBoundaryDecision.

Definition decideSystemsControlByFacts
  (branchAccepted stateAccepted protocolAccepted boundaryAccepted : bool)
  : SystemsControlDecision :=
  if branchAccepted then
    if stateAccepted then
      if protocolAccepted then
        if boundaryAccepted
        then SystemsControlAcceptedDecision
        else SystemsControlBoundaryDecision
      else SystemsControlProtocolDecision
    else SystemsControlStateDecision
  else SystemsControlBranchDecision.

Definition reflectedSystemsControlFacts
  (branchFacts : BranchPreservationFacts)
  (stateFacts : StateProjectionFacts)
  (protocolFacts : ProtocolPreservationFacts)
  (boundaryFacts : BoundaryCommitFacts)
  : SystemsControlFacts :=
  {| systemsBranchFacts := branchFacts;
     systemsStateFacts := stateFacts;
     systemsProtocolFacts := protocolFacts;
     systemsBoundaryFacts := boundaryFacts |}.

Theorem reflected_systems_control_decision_exact :
  forall branchFacts stateFacts protocolFacts boundaryFacts
         branchAccepted stateAccepted protocolAccepted boundaryAccepted,
    (branchAccepted = true <-> branchPreserved branchFacts) ->
    (stateAccepted = true <-> stateProjectionPreserved stateFacts) ->
    (protocolAccepted = true <-> protocolPreserved protocolFacts) ->
    (boundaryAccepted = true <-> boundaryCommitPreserved boundaryFacts) ->
    decideSystemsControlByFacts
      branchAccepted stateAccepted protocolAccepted boundaryAccepted =
      SystemsControlAcceptedDecision <->
    systemsControlPreserved
      (reflectedSystemsControlFacts branchFacts stateFacts protocolFacts boundaryFacts).
Proof.
  intros branchFacts stateFacts protocolFacts boundaryFacts
    branchAccepted stateAccepted protocolAccepted boundaryAccepted
    Hbranch Hstate Hprotocol Hboundary.
  unfold decideSystemsControlByFacts, systemsControlPreserved,
    reflectedSystemsControlFacts.
  destruct branchAccepted;
  destruct stateAccepted;
  destruct protocolAccepted;
  destruct boundaryAccepted;
  simpl in *; intuition discriminate.
Qed.
