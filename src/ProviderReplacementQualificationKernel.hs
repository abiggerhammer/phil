module ProviderReplacementQualificationKernel where

import qualified Prelude

data ProviderReplacementDecision =
   ProviderReplacementAccepted
 | ProviderReplacementAdmissionRequired
 | ProviderReplacementInterfaceMismatch
 | ProviderReplacementOccurrenceMismatch
 | ProviderReplacementInstanceMismatch
 | ProviderReplacementSameSemanticSubject
 | ProviderReplacementRealizationUnchanged
 | ProviderReplacementClaimLineageInherited
 | ProviderReplacementEvidenceLineageInherited
 | ProviderReplacementAdmissionLineageInherited
 | ProviderReplacementSharedEvidenceWithoutScope
 | ProviderReplacementUnexpectedEvidenceReuse

decideProviderReplacementByFacts :: Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    ProviderReplacementDecision
decideProviderReplacementByFacts priorAdmitted replacementAdmitted interfaceMatches occurrenceMatches instanceMatches subjectDiffers realizationDiffers claimDiffers evidenceDiffers admissionDiffers allSharedEvidenceScoped noUnexpectedReuse =
  case priorAdmitted of {
   Prelude.True ->
    case replacementAdmitted of {
     Prelude.True ->
      case interfaceMatches of {
       Prelude.True ->
        case occurrenceMatches of {
         Prelude.True ->
          case instanceMatches of {
           Prelude.True ->
            case subjectDiffers of {
             Prelude.True ->
              case realizationDiffers of {
               Prelude.True ->
                case claimDiffers of {
                 Prelude.True ->
                  case evidenceDiffers of {
                   Prelude.True ->
                    case admissionDiffers of {
                     Prelude.True ->
                      case allSharedEvidenceScoped of {
                       Prelude.True ->
                        case noUnexpectedReuse of {
                         Prelude.True -> ProviderReplacementAccepted;
                         Prelude.False ->
                          ProviderReplacementUnexpectedEvidenceReuse};
                       Prelude.False ->
                        ProviderReplacementSharedEvidenceWithoutScope};
                     Prelude.False ->
                      ProviderReplacementAdmissionLineageInherited};
                   Prelude.False ->
                    ProviderReplacementEvidenceLineageInherited};
                 Prelude.False -> ProviderReplacementClaimLineageInherited};
               Prelude.False -> ProviderReplacementRealizationUnchanged};
             Prelude.False -> ProviderReplacementSameSemanticSubject};
           Prelude.False -> ProviderReplacementInstanceMismatch};
         Prelude.False -> ProviderReplacementOccurrenceMismatch};
       Prelude.False -> ProviderReplacementInterfaceMismatch};
     Prelude.False -> ProviderReplacementAdmissionRequired};
   Prelude.False -> ProviderReplacementAdmissionRequired}

data ProviderReplacementReuseDecision =
   ProviderReplacementReuseAccepted
 | ProviderReplacementReuseReferenceMismatch
 | ProviderReplacementReusePriorClaimMismatch
 | ProviderReplacementReuseNewClaimMismatch
 | ProviderReplacementReuseScopeMissing

decideProviderReplacementReuseByFacts :: Prelude.Bool -> Prelude.Bool ->
                                         Prelude.Bool -> Prelude.Bool ->
                                         ProviderReplacementReuseDecision
decideProviderReplacementReuseByFacts referenceMatches priorClaimMatches newClaimMatches hasValidityScope =
  case referenceMatches of {
   Prelude.True ->
    case priorClaimMatches of {
     Prelude.True ->
      case newClaimMatches of {
       Prelude.True ->
        case hasValidityScope of {
         Prelude.True -> ProviderReplacementReuseAccepted;
         Prelude.False -> ProviderReplacementReuseScopeMissing};
       Prelude.False -> ProviderReplacementReuseNewClaimMismatch};
     Prelude.False -> ProviderReplacementReusePriorClaimMismatch};
   Prelude.False -> ProviderReplacementReuseReferenceMismatch}

