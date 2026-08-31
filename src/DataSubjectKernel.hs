module DataSubjectKernel where

import qualified Prelude

data DataSubjectPrerequisiteDecision =
   DataSubjectPrerequisitesAccepted
 | DataSubjectPriorNotConsumedDecision
 | DataSubjectReplacementNotConstructedDecision
 | DataSubjectPriorNotStableDecision
 | DataSubjectReplacementNotStableDecision
 | DataSubjectKindMismatchDecision
 | DataSubjectEvidenceTemplateMissingSubjectDecision
 | DataSubjectEvidencePriorMismatchDecision
 | DataSubjectEvidenceNotStableDecision
 | DataSubjectEvidenceKindMismatchDecision

decideDataSubjectPrerequisites :: Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool ->
                                  DataSubjectPrerequisiteDecision
decideDataSubjectPrerequisites priorConsumed replacementConstructed priorStable replacementStable kindsMatch evidenceTemplateMentionsSubject evidenceMatchesPrior evidenceStable evidenceKindMatchesPrior =
  case priorConsumed of {
   Prelude.True ->
    case replacementConstructed of {
     Prelude.True ->
      case priorStable of {
       Prelude.True ->
        case replacementStable of {
         Prelude.True ->
          case kindsMatch of {
           Prelude.True ->
            case evidenceTemplateMentionsSubject of {
             Prelude.True ->
              case evidenceMatchesPrior of {
               Prelude.True ->
                case evidenceStable of {
                 Prelude.True ->
                  case evidenceKindMatchesPrior of {
                   Prelude.True -> DataSubjectPrerequisitesAccepted;
                   Prelude.False -> DataSubjectEvidenceKindMismatchDecision};
                 Prelude.False -> DataSubjectEvidenceNotStableDecision};
               Prelude.False -> DataSubjectEvidencePriorMismatchDecision};
             Prelude.False ->
              DataSubjectEvidenceTemplateMissingSubjectDecision};
           Prelude.False -> DataSubjectKindMismatchDecision};
         Prelude.False -> DataSubjectReplacementNotStableDecision};
       Prelude.False -> DataSubjectPriorNotStableDecision};
     Prelude.False -> DataSubjectReplacementNotConstructedDecision};
   Prelude.False -> DataSubjectPriorNotConsumedDecision}

data DataSubjectTransportModeDecision =
   DataSubjectTransportModeAccepted
 | DataSubjectUnexpectedTransportDecision
 | DataSubjectTransportRequiredDecision

decideDataSubjectTransportMode :: Prelude.Bool -> Prelude.Bool ->
                                  DataSubjectTransportModeDecision
decideDataSubjectTransportMode sameSubject transportPresent =
  case sameSubject of {
   Prelude.True ->
    case transportPresent of {
     Prelude.True -> DataSubjectUnexpectedTransportDecision;
     Prelude.False -> DataSubjectTransportModeAccepted};
   Prelude.False ->
    case transportPresent of {
     Prelude.True -> DataSubjectTransportModeAccepted;
     Prelude.False -> DataSubjectTransportRequiredDecision}}

data DataSubjectTransportDecision =
   DataSubjectTransportAcceptedDecision
 | DataSubjectTransportDispositionRejectedDecision
 | DataSubjectTransportRevisionMissingDecision
 | DataSubjectTransportEvidenceMismatchDecision
 | DataSubjectTransportPriorMismatchDecision
 | DataSubjectTransportReplacementMismatchDecision
 | DataSubjectTransportSourcePropositionMismatchDecision
 | DataSubjectTransportTargetPropositionMismatchDecision

decideDataSubjectTransport :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              Prelude.Bool -> DataSubjectTransportDecision
decideDataSubjectTransport dispositionAccepted revisionNonempty evidenceReferenceMatches priorIdentityMatches replacementIdentityMatches sourcePropositionMatches targetPropositionMatches =
  case dispositionAccepted of {
   Prelude.True ->
    case revisionNonempty of {
     Prelude.True ->
      case evidenceReferenceMatches of {
       Prelude.True ->
        case priorIdentityMatches of {
         Prelude.True ->
          case replacementIdentityMatches of {
           Prelude.True ->
            case sourcePropositionMatches of {
             Prelude.True ->
              case targetPropositionMatches of {
               Prelude.True -> DataSubjectTransportAcceptedDecision;
               Prelude.False ->
                DataSubjectTransportTargetPropositionMismatchDecision};
             Prelude.False ->
              DataSubjectTransportSourcePropositionMismatchDecision};
           Prelude.False -> DataSubjectTransportReplacementMismatchDecision};
         Prelude.False -> DataSubjectTransportPriorMismatchDecision};
       Prelude.False -> DataSubjectTransportEvidenceMismatchDecision};
     Prelude.False -> DataSubjectTransportRevisionMissingDecision};
   Prelude.False -> DataSubjectTransportDispositionRejectedDecision}

