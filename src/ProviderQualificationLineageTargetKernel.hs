module ProviderQualificationLineageTargetKernel where

import qualified Prelude

data TargetReuseDecision =
   TargetReuseAcceptedDecision
 | TargetReuseSemanticLayerDecision
 | TargetReuseSemanticSubjectDecision
 | TargetReusePriorClaimDecision
 | TargetReusePriorInterfaceDecision
 | TargetReusePriorImplementationDecision
 | TargetReusePriorTranslationDecision
 | TargetReuseNewClaimDecision
 | TargetReuseNewInterfaceDecision
 | TargetReuseNewImplementationDecision
 | TargetReuseNewTranslationDecision
 | TargetReuseDistinctProfileDecision

decideTargetReuseByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                            Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                            Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                            Prelude.Bool -> Prelude.Bool ->
                            TargetReuseDecision
decideTargetReuseByFacts semanticLayer semanticSubject priorClaim priorInterface priorImplementation priorTranslation newClaim newInterface newImplementation newTranslation distinctProfiles =
  case semanticLayer of {
   Prelude.True ->
    case semanticSubject of {
     Prelude.True ->
      case priorClaim of {
       Prelude.True ->
        case priorInterface of {
         Prelude.True ->
          case priorImplementation of {
           Prelude.True ->
            case priorTranslation of {
             Prelude.True ->
              case newClaim of {
               Prelude.True ->
                case newInterface of {
                 Prelude.True ->
                  case newImplementation of {
                   Prelude.True ->
                    case newTranslation of {
                     Prelude.True ->
                      case distinctProfiles of {
                       Prelude.True -> TargetReuseAcceptedDecision;
                       Prelude.False -> TargetReuseDistinctProfileDecision};
                     Prelude.False -> TargetReuseNewTranslationDecision};
                   Prelude.False -> TargetReuseNewImplementationDecision};
                 Prelude.False -> TargetReuseNewInterfaceDecision};
               Prelude.False -> TargetReuseNewClaimDecision};
             Prelude.False -> TargetReusePriorTranslationDecision};
           Prelude.False -> TargetReusePriorImplementationDecision};
         Prelude.False -> TargetReusePriorInterfaceDecision};
       Prelude.False -> TargetReusePriorClaimDecision};
     Prelude.False -> TargetReuseSemanticSubjectDecision};
   Prelude.False -> TargetReuseSemanticLayerDecision}

data AdmissionApplicabilityDecision =
   AdmissionApplicabilityAcceptedDecision
 | AdmissionApplicabilityRejectedDecision
 | AdmissionApplicabilityAdmissionRevisionDecision
 | AdmissionApplicabilityClaimRevisionDecision
 | AdmissionApplicabilityTargetEvidenceRevisionDecision
 | AdmissionApplicabilityTargetEvidenceClaimDecision
 | AdmissionApplicabilityInterfaceEvidenceDecision
 | AdmissionApplicabilityImplementationEvidenceDecision
 | AdmissionApplicabilityTargetEvidenceDecision
 | AdmissionApplicabilityArtifactEvidenceDecision
 | AdmissionApplicabilityAbiEvidenceDecision
 | AdmissionApplicabilitySelectedAdmissionDecision
 | AdmissionApplicabilitySelectedEvidenceDecision
 | AdmissionApplicabilitySelectedOccurrenceDecision
 | AdmissionApplicabilitySelectedInstanceDecision
 | AdmissionApplicabilitySelectedRealizationDecision
 | AdmissionApplicabilitySelectedInterfaceDecision
 | AdmissionApplicabilitySelectedImplementationDecision
 | AdmissionApplicabilitySelectedTargetDecision
 | AdmissionApplicabilitySelectedArtifactDecision
 | AdmissionApplicabilitySelectedAbiDecision

decideAdmissionApplicabilityByFacts :: Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       Prelude.Bool -> Prelude.Bool ->
                                       AdmissionApplicabilityDecision
decideAdmissionApplicabilityByFacts admitted admissionRevision claimRevision targetEvidenceRevision targetEvidenceClaim interfaceEvidence implementationEvidence targetEvidence artifactEvidence abiEvidence selectedAdmission selectedEvidence selectedOccurrence selectedInstance selectedRealization selectedInterface selectedImplementation selectedTarget selectedArtifact selectedAbi =
  case admitted of {
   Prelude.True ->
    case admissionRevision of {
     Prelude.True ->
      case claimRevision of {
       Prelude.True ->
        case targetEvidenceRevision of {
         Prelude.True ->
          case targetEvidenceClaim of {
           Prelude.True ->
            case interfaceEvidence of {
             Prelude.True ->
              case implementationEvidence of {
               Prelude.True ->
                case targetEvidence of {
                 Prelude.True ->
                  case artifactEvidence of {
                   Prelude.True ->
                    case abiEvidence of {
                     Prelude.True ->
                      case selectedAdmission of {
                       Prelude.True ->
                        case selectedEvidence of {
                         Prelude.True ->
                          case selectedOccurrence of {
                           Prelude.True ->
                            case selectedInstance of {
                             Prelude.True ->
                              case selectedRealization of {
                               Prelude.True ->
                                case selectedInterface of {
                                 Prelude.True ->
                                  case selectedImplementation of {
                                   Prelude.True ->
                                    case selectedTarget of {
                                     Prelude.True ->
                                      case selectedArtifact of {
                                       Prelude.True ->
                                        case selectedAbi of {
                                         Prelude.True ->
                                          AdmissionApplicabilityAcceptedDecision;
                                         Prelude.False ->
                                          AdmissionApplicabilitySelectedAbiDecision};
                                       Prelude.False ->
                                        AdmissionApplicabilitySelectedArtifactDecision};
                                     Prelude.False ->
                                      AdmissionApplicabilitySelectedTargetDecision};
                                   Prelude.False ->
                                    AdmissionApplicabilitySelectedImplementationDecision};
                                 Prelude.False ->
                                  AdmissionApplicabilitySelectedInterfaceDecision};
                               Prelude.False ->
                                AdmissionApplicabilitySelectedRealizationDecision};
                             Prelude.False ->
                              AdmissionApplicabilitySelectedInstanceDecision};
                           Prelude.False ->
                            AdmissionApplicabilitySelectedOccurrenceDecision};
                         Prelude.False ->
                          AdmissionApplicabilitySelectedEvidenceDecision};
                       Prelude.False ->
                        AdmissionApplicabilitySelectedAdmissionDecision};
                     Prelude.False ->
                      AdmissionApplicabilityAbiEvidenceDecision};
                   Prelude.False ->
                    AdmissionApplicabilityArtifactEvidenceDecision};
                 Prelude.False ->
                  AdmissionApplicabilityTargetEvidenceDecision};
               Prelude.False ->
                AdmissionApplicabilityImplementationEvidenceDecision};
             Prelude.False -> AdmissionApplicabilityInterfaceEvidenceDecision};
           Prelude.False -> AdmissionApplicabilityTargetEvidenceClaimDecision};
         Prelude.False ->
          AdmissionApplicabilityTargetEvidenceRevisionDecision};
       Prelude.False -> AdmissionApplicabilityClaimRevisionDecision};
     Prelude.False -> AdmissionApplicabilityAdmissionRevisionDecision};
   Prelude.False -> AdmissionApplicabilityRejectedDecision}

