module SystemsStageClosureKernel where

import qualified Prelude

data SourceClosureDecision =
   SourceClosureAcceptedDecision
 | SourceClosureCoverageDecision
 | SourceClosureEmptyFactDecision
 | SourceClosureDispositionDecision

decideSourceClosureByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              SourceClosureDecision
decideSourceClosureByFacts coverageExact noEmptyFact dispositionsPermitted =
  case coverageExact of {
   Prelude.True ->
    case noEmptyFact of {
     Prelude.True ->
      case dispositionsPermitted of {
       Prelude.True -> SourceClosureAcceptedDecision;
       Prelude.False -> SourceClosureDispositionDecision};
     Prelude.False -> SourceClosureEmptyFactDecision};
   Prelude.False -> SourceClosureCoverageDecision}

data TargetClosureDecision =
   TargetClosureAcceptedDecision
 | TargetClosureCoverageDecision
 | TargetClosureEmptyMechanismDecision
 | TargetClosureJustificationDecision

decideTargetClosureByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              TargetClosureDecision
decideTargetClosureByFacts coverageExact noEmptyMechanism justificationsValid =
  case coverageExact of {
   Prelude.True ->
    case noEmptyMechanism of {
     Prelude.True ->
      case justificationsValid of {
       Prelude.True -> TargetClosureAcceptedDecision;
       Prelude.False -> TargetClosureJustificationDecision};
     Prelude.False -> TargetClosureEmptyMechanismDecision};
   Prelude.False -> TargetClosureCoverageDecision}

data StageIdentityDecision =
   StageIdentityAcceptedDecision
 | StageIdentitySubjectDecision
 | StageIdentityInstanceDecision
 | StageIdentityRealizationDecision
 | StageIdentitySystemsDecision
 | StageIdentityContractDecision
 | StageIdentityProfileDecision
 | StageIdentityRecomputedSystemsDecision
 | StageIdentityRecomputedFinalDecision
 | StageIdentityStoredSystemsDecision
 | StageIdentityStoredFinalDecision

decideStageIdentityByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              Prelude.Bool -> StageIdentityDecision
decideStageIdentityByFacts subjectExact instanceExact realizationExact systemsExact contractExact profileExact recomputedSystemsExact recomputedFinalExact storedSystemsPresent storedFinalPresent =
  case subjectExact of {
   Prelude.True ->
    case instanceExact of {
     Prelude.True ->
      case realizationExact of {
       Prelude.True ->
        case systemsExact of {
         Prelude.True ->
          case contractExact of {
           Prelude.True ->
            case profileExact of {
             Prelude.True ->
              case recomputedSystemsExact of {
               Prelude.True ->
                case recomputedFinalExact of {
                 Prelude.True ->
                  case storedSystemsPresent of {
                   Prelude.True ->
                    case storedFinalPresent of {
                     Prelude.True -> StageIdentityAcceptedDecision;
                     Prelude.False -> StageIdentityStoredFinalDecision};
                   Prelude.False -> StageIdentityStoredSystemsDecision};
                 Prelude.False -> StageIdentityRecomputedFinalDecision};
               Prelude.False -> StageIdentityRecomputedSystemsDecision};
             Prelude.False -> StageIdentityProfileDecision};
           Prelude.False -> StageIdentityContractDecision};
         Prelude.False -> StageIdentitySystemsDecision};
       Prelude.False -> StageIdentityRealizationDecision};
     Prelude.False -> StageIdentityInstanceDecision};
   Prelude.False -> StageIdentitySubjectDecision}

data SystemsStageClosureDecision =
   SystemsStageClosureAcceptedDecision
 | SystemsStageClosureFactDecision
 | SystemsStageClosureProjectionDecision
 | SystemsStageClosureSourceDecision
 | SystemsStageClosureTargetDecision
 | SystemsStageClosureScopeDecision
 | SystemsStageClosureIdentityDecision

decideSystemsStageClosureByFacts :: Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    SystemsStageClosureDecision
decideSystemsStageClosureByFacts factVerificationAccepted factProjectionExact sourceClosureAccepted targetClosureAccepted scopeMatchesAccepted finalIdentityAccepted =
  case factVerificationAccepted of {
   Prelude.True ->
    case factProjectionExact of {
     Prelude.True ->
      case sourceClosureAccepted of {
       Prelude.True ->
        case targetClosureAccepted of {
         Prelude.True ->
          case scopeMatchesAccepted of {
           Prelude.True ->
            case finalIdentityAccepted of {
             Prelude.True -> SystemsStageClosureAcceptedDecision;
             Prelude.False -> SystemsStageClosureIdentityDecision};
           Prelude.False -> SystemsStageClosureScopeDecision};
         Prelude.False -> SystemsStageClosureTargetDecision};
       Prelude.False -> SystemsStageClosureSourceDecision};
     Prelude.False -> SystemsStageClosureProjectionDecision};
   Prelude.False -> SystemsStageClosureFactDecision}

