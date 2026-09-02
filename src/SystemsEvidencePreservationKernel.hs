{-# OPTIONS_GHC -Wno-unused-imports #-}
module SystemsEvidencePreservationKernel where

import qualified Prelude

data Bool =
   True
 | False

data EvidenceErasureDecision =
   EvidenceErasureAcceptedDecision
 | EvidenceErasureAssuranceUseDecision
 | EvidenceErasureSourceSubjectDecision
 | EvidenceErasureDischargeSubjectDecision
 | EvidenceErasureRepresentationDecision
 | EvidenceErasureLastUseDecision
 | EvidenceErasureConsumerClosureBasisDecision
 | EvidenceErasureSuccessorRevisionDecision
 | EvidenceErasureRuntimeResidueRevisionDecision
 | EvidenceErasureCostRevisionDecision
 | EvidenceErasureLaterConsumersDecision

decideEvidenceErasureByFacts :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool
                                -> Bool -> Bool -> Bool -> Bool ->
                                EvidenceErasureDecision
decideEvidenceErasureByFacts assuranceUseAccepted sourceSubjectExact dischargeSubjectExact representationPresent lastUsePresent consumerClosureBasisPresent successorRevisionWellFormed runtimeResidueRevisionWellFormed costRevisionWellFormed laterConsumersClosed =
  case assuranceUseAccepted of {
   True ->
    case sourceSubjectExact of {
     True ->
      case dischargeSubjectExact of {
       True ->
        case representationPresent of {
         True ->
          case lastUsePresent of {
           True ->
            case consumerClosureBasisPresent of {
             True ->
              case successorRevisionWellFormed of {
               True ->
                case runtimeResidueRevisionWellFormed of {
                 True ->
                  case costRevisionWellFormed of {
                   True ->
                    case laterConsumersClosed of {
                     True -> EvidenceErasureAcceptedDecision;
                     False -> EvidenceErasureLaterConsumersDecision};
                   False -> EvidenceErasureCostRevisionDecision};
                 False -> EvidenceErasureRuntimeResidueRevisionDecision};
               False -> EvidenceErasureSuccessorRevisionDecision};
             False -> EvidenceErasureConsumerClosureBasisDecision};
           False -> EvidenceErasureLastUseDecision};
         False -> EvidenceErasureRepresentationDecision};
       False -> EvidenceErasureDischargeSubjectDecision};
     False -> EvidenceErasureSourceSubjectDecision};
   False -> EvidenceErasureAssuranceUseDecision}

data AssumptionDependencyDecision =
   AssumptionDependencyAcceptedDecision
 | AssumptionRegistryDecision
 | AssumptionAuthorityDecision
 | AssumptionValidityScopeDecision
 | AssumptionForwardDecision
 | AssumptionForwardScopeDecision
 | AssumptionReverseDecision

decideAssumptionDependencyByFacts :: Bool -> Bool -> Bool -> Bool -> Bool ->
                                     Bool -> AssumptionDependencyDecision
decideAssumptionDependencyByFacts registryExact authorityAccepted validityScopesPresent forwardExact forwardScopesExact reverseExact =
  case registryExact of {
   True ->
    case authorityAccepted of {
     True ->
      case validityScopesPresent of {
       True ->
        case forwardExact of {
         True ->
          case forwardScopesExact of {
           True ->
            case reverseExact of {
             True -> AssumptionDependencyAcceptedDecision;
             False -> AssumptionReverseDecision};
           False -> AssumptionForwardScopeDecision};
         False -> AssumptionForwardDecision};
       False -> AssumptionValidityScopeDecision};
     False -> AssumptionAuthorityDecision};
   False -> AssumptionRegistryDecision}

data SystemsEvidenceDecision =
   SystemsEvidenceAcceptedDecision
 | SystemsEvidenceSubjectTransferDecision
 | SystemsEvidenceErasureDecision
 | SystemsEvidenceAssumptionDecision

decideSystemsEvidenceByFacts :: Bool -> Bool -> Bool ->
                                SystemsEvidenceDecision
decideSystemsEvidenceByFacts subjectTransferAccepted erasureAccepted assumptionsAccepted =
  case subjectTransferAccepted of {
   True ->
    case erasureAccepted of {
     True ->
      case assumptionsAccepted of {
       True -> SystemsEvidenceAcceptedDecision;
       False -> SystemsEvidenceAssumptionDecision};
     False -> SystemsEvidenceErasureDecision};
   False -> SystemsEvidenceSubjectTransferDecision}

