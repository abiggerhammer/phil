module ProviderEvidenceQualificationKernel where

import qualified Prelude

data ProviderEvidenceCompetenceDecision =
   ProviderEvidenceCompetenceAccepted
 | ProviderEvidenceOperationNotQualified
 | ProviderEvidenceOperationMismatch
 | ProviderEvidenceFamilyMismatch
 | ProviderEvidenceParametersMismatch
 | ProviderEvidenceStableSubjectMismatch
 | ProviderEvidenceValidityMismatch

decideProviderEvidenceCompetenceByFacts :: Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool -> Prelude.Bool ->
                                           ProviderEvidenceCompetenceDecision
decideProviderEvidenceCompetenceByFacts operationQualified operationMatches familyMatches parametersMatch stableSubjectMatches validityMatches =
  case operationQualified of {
   Prelude.True ->
    case operationMatches of {
     Prelude.True ->
      case familyMatches of {
       Prelude.True ->
        case parametersMatch of {
         Prelude.True ->
          case stableSubjectMatches of {
           Prelude.True ->
            case validityMatches of {
             Prelude.True -> ProviderEvidenceCompetenceAccepted;
             Prelude.False -> ProviderEvidenceValidityMismatch};
           Prelude.False -> ProviderEvidenceStableSubjectMismatch};
         Prelude.False -> ProviderEvidenceParametersMismatch};
       Prelude.False -> ProviderEvidenceFamilyMismatch};
     Prelude.False -> ProviderEvidenceOperationMismatch};
   Prelude.False -> ProviderEvidenceOperationNotQualified}

data ProviderEvidenceMappingDecision =
   ProviderEvidenceMappingAccepted
 | ProviderEvidenceDirectMappingRejected
 | ProviderEvidenceCheckedObservationMismatch
 | ProviderEvidenceCheckedSubjectMismatch
 | ProviderEvidenceRuntimeCoincidenceRejected

decideDirectEvidenceSubjectMappingByFacts :: Prelude.Bool -> Prelude.Bool ->
                                             ProviderEvidenceMappingDecision
decideDirectEvidenceSubjectMappingByFacts observationIsExactStable mappedSubjectMatches =
  case observationIsExactStable of {
   Prelude.True ->
    case mappedSubjectMatches of {
     Prelude.True -> ProviderEvidenceMappingAccepted;
     Prelude.False -> ProviderEvidenceDirectMappingRejected};
   Prelude.False -> ProviderEvidenceDirectMappingRejected}

decideCheckedEvidenceSubjectMappingByFacts :: Prelude.Bool -> Prelude.Bool ->
                                              ProviderEvidenceMappingDecision
decideCheckedEvidenceSubjectMappingByFacts observationMatches mappedSubjectMatches =
  case observationMatches of {
   Prelude.True ->
    case mappedSubjectMatches of {
     Prelude.True -> ProviderEvidenceMappingAccepted;
     Prelude.False -> ProviderEvidenceCheckedSubjectMismatch};
   Prelude.False -> ProviderEvidenceCheckedObservationMismatch}

decideRuntimeCoincidenceSubjectMapping :: ProviderEvidenceMappingDecision
decideRuntimeCoincidenceSubjectMapping =
  ProviderEvidenceRuntimeCoincidenceRejected
