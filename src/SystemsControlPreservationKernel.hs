module SystemsControlPreservationKernel where

import qualified Prelude

data BranchPreservationDecision =
   BranchPreservationAcceptedDecision
 | BranchOutcomeDomainDecision
 | BranchOwnerFateDomainDecision
 | BranchOwnerFateRealizationDecision
 | BranchControlClassDecision
 | BranchTrackedOwnerDecision

decideBranchPreservationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                   Prelude.Bool -> Prelude.Bool ->
                                   Prelude.Bool -> BranchPreservationDecision
decideBranchPreservationByFacts outcomeDomainExact ownerFateDomainExact ownerFateRealizedExactlyOnce controlClassExact trackedValuesAreOwners =
  case outcomeDomainExact of {
   Prelude.True ->
    case ownerFateDomainExact of {
     Prelude.True ->
      case ownerFateRealizedExactlyOnce of {
       Prelude.True ->
        case controlClassExact of {
         Prelude.True ->
          case trackedValuesAreOwners of {
           Prelude.True -> BranchPreservationAcceptedDecision;
           Prelude.False -> BranchTrackedOwnerDecision};
         Prelude.False -> BranchControlClassDecision};
       Prelude.False -> BranchOwnerFateRealizationDecision};
     Prelude.False -> BranchOwnerFateDomainDecision};
   Prelude.False -> BranchOutcomeDomainDecision}

data StateProjectionDecision =
   StateProjectionAcceptedDecision
 | StateProjectionKindDecision
 | StateSlotDomainDecision
 | StateRestrictedOwnerModeDecision
 | StateFixedSubjectDecision
 | StateRestrictedOwnerUniqueDecision
 | StateLinearOwnersCoveredDecision
 | StateScopedLoanEscapeDecision
 | ClosureCaptureCarrierDecision
 | ClosureCarrierSharingDecision

decideStateProjectionByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool -> Prelude.Bool ->
                                Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool -> StateProjectionDecision
decideStateProjectionByFacts projectionKindExact slotDomainExact restrictedOwnerModeExact fixedSubjectExact restrictedOwnerUnique linearOwnersCovered scopedLoansDoNotEscape restrictedCaptureHasOneCarrier restrictedCarriersAreUnshared =
  case projectionKindExact of {
   Prelude.True ->
    case slotDomainExact of {
     Prelude.True ->
      case restrictedOwnerModeExact of {
       Prelude.True ->
        case fixedSubjectExact of {
         Prelude.True ->
          case restrictedOwnerUnique of {
           Prelude.True ->
            case linearOwnersCovered of {
             Prelude.True ->
              case scopedLoansDoNotEscape of {
               Prelude.True ->
                case restrictedCaptureHasOneCarrier of {
                 Prelude.True ->
                  case restrictedCarriersAreUnshared of {
                   Prelude.True -> StateProjectionAcceptedDecision;
                   Prelude.False -> ClosureCarrierSharingDecision};
                 Prelude.False -> ClosureCaptureCarrierDecision};
               Prelude.False -> StateScopedLoanEscapeDecision};
             Prelude.False -> StateLinearOwnersCoveredDecision};
           Prelude.False -> StateRestrictedOwnerUniqueDecision};
         Prelude.False -> StateFixedSubjectDecision};
       Prelude.False -> StateRestrictedOwnerModeDecision};
     Prelude.False -> StateSlotDomainDecision};
   Prelude.False -> StateProjectionKindDecision}

data ProtocolPreservationDecision =
   ProtocolPreservationAcceptedDecision
 | ProtocolBasisDecision
 | ProtocolTargetSiteDecision
 | ProtocolTransportUseDecision
 | ProtocolOutcomeDomainDecision
 | ProtocolInstanceDecision
 | ProtocolRoleDecision
 | ProtocolSuccessorFreshDecision
 | ProtocolPredecessorConsumedDecision
 | ProtocolSuccessorProducedDecision
 | ProtocolLineageDecision

decideProtocolPreservationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool ->
                                     ProtocolPreservationDecision
decideProtocolPreservationByFacts basisIsChecked targetSiteExact transportUseExact outcomeDomainExact instanceExact roleExact successorIsFresh predecessorConsumedOnce successorProducedOnce lineageAcyclic =
  case basisIsChecked of {
   Prelude.True ->
    case targetSiteExact of {
     Prelude.True ->
      case transportUseExact of {
       Prelude.True ->
        case outcomeDomainExact of {
         Prelude.True ->
          case instanceExact of {
           Prelude.True ->
            case roleExact of {
             Prelude.True ->
              case successorIsFresh of {
               Prelude.True ->
                case predecessorConsumedOnce of {
                 Prelude.True ->
                  case successorProducedOnce of {
                   Prelude.True ->
                    case lineageAcyclic of {
                     Prelude.True -> ProtocolPreservationAcceptedDecision;
                     Prelude.False -> ProtocolLineageDecision};
                   Prelude.False -> ProtocolSuccessorProducedDecision};
                 Prelude.False -> ProtocolPredecessorConsumedDecision};
               Prelude.False -> ProtocolSuccessorFreshDecision};
             Prelude.False -> ProtocolRoleDecision};
           Prelude.False -> ProtocolInstanceDecision};
         Prelude.False -> ProtocolOutcomeDomainDecision};
       Prelude.False -> ProtocolTransportUseDecision};
     Prelude.False -> ProtocolTargetSiteDecision};
   Prelude.False -> ProtocolBasisDecision}

data BoundaryCommitDecision =
   BoundaryCommitAcceptedDecision
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
 | BoundaryCompleteBeforeSuccessDecision

decideBoundaryCommitByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                               -> Prelude.Bool -> Prelude.Bool ->
                               Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                               -> Prelude.Bool -> Prelude.Bool ->
                               Prelude.Bool -> BoundaryCommitDecision
decideBoundaryCommitByFacts sourceRuntimeFactExact transportExact ownerExact subjectExact lengthExact runtimeKindExact runtimeRevisionEvidenceExact protocolTransitionExact commitProducesSuccessor failureRemainsTerminal completeBeforeSuccess =
  case sourceRuntimeFactExact of {
   Prelude.True ->
    case transportExact of {
     Prelude.True ->
      case ownerExact of {
       Prelude.True ->
        case subjectExact of {
         Prelude.True ->
          case lengthExact of {
           Prelude.True ->
            case runtimeKindExact of {
             Prelude.True ->
              case runtimeRevisionEvidenceExact of {
               Prelude.True ->
                case protocolTransitionExact of {
                 Prelude.True ->
                  case commitProducesSuccessor of {
                   Prelude.True ->
                    case failureRemainsTerminal of {
                     Prelude.True ->
                      case completeBeforeSuccess of {
                       Prelude.True -> BoundaryCommitAcceptedDecision;
                       Prelude.False -> BoundaryCompleteBeforeSuccessDecision};
                     Prelude.False -> BoundaryFailureTerminalDecision};
                   Prelude.False -> BoundaryCommitSuccessorDecision};
                 Prelude.False -> BoundaryProtocolTransitionDecision};
               Prelude.False -> BoundaryRuntimeRevisionEvidenceDecision};
             Prelude.False -> BoundaryRuntimeKindDecision};
           Prelude.False -> BoundaryLengthDecision};
         Prelude.False -> BoundarySubjectDecision};
       Prelude.False -> BoundaryOwnerDecision};
     Prelude.False -> BoundaryTransportDecision};
   Prelude.False -> BoundarySourceRuntimeFactDecision}

data SystemsControlDecision =
   SystemsControlAcceptedDecision
 | SystemsControlBranchDecision
 | SystemsControlStateDecision
 | SystemsControlProtocolDecision
 | SystemsControlBoundaryDecision

decideSystemsControlByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                               -> Prelude.Bool -> SystemsControlDecision
decideSystemsControlByFacts branchAccepted stateAccepted protocolAccepted boundaryAccepted =
  case branchAccepted of {
   Prelude.True ->
    case stateAccepted of {
     Prelude.True ->
      case protocolAccepted of {
       Prelude.True ->
        case boundaryAccepted of {
         Prelude.True -> SystemsControlAcceptedDecision;
         Prelude.False -> SystemsControlBoundaryDecision};
       Prelude.False -> SystemsControlProtocolDecision};
     Prelude.False -> SystemsControlStateDecision};
   Prelude.False -> SystemsControlBranchDecision}

