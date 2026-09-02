module SystemsRealizationEffectsKernel where

import qualified Prelude

data TargetStrengtheningDecision =
   TargetStrengtheningAcceptedDecision
 | TargetStrengtheningCoverageDecision
 | TargetStrengtheningIntroducerDecision
 | TargetStrengtheningSourceAssuranceDecision
 | TargetStrengtheningDerivedRequiredDecision
 | TargetStrengtheningDerivedRevisionDecision
 | TargetStrengtheningDerivedIntroducerDecision
 | TargetStrengtheningDerivedSubjectDecision
 | TargetStrengtheningDerivedStatementDecision
 | TargetStrengtheningDerivedAcceptanceDecision

decideTargetStrengtheningByFacts :: Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool ->
                                    TargetStrengtheningDecision
decideTargetStrengtheningByFacts coverageExact introducerPresent sourceAssuranceValid derivedRequirementSatisfied derivedRevisionPresent derivedIntroducerExact derivedSubjectPresent derivedStatementPresent derivedAcceptancePresent =
  case coverageExact of {
   Prelude.True ->
    case introducerPresent of {
     Prelude.True ->
      case sourceAssuranceValid of {
       Prelude.True ->
        case derivedRequirementSatisfied of {
         Prelude.True ->
          case derivedRevisionPresent of {
           Prelude.True ->
            case derivedIntroducerExact of {
             Prelude.True ->
              case derivedSubjectPresent of {
               Prelude.True ->
                case derivedStatementPresent of {
                 Prelude.True ->
                  case derivedAcceptancePresent of {
                   Prelude.True -> TargetStrengtheningAcceptedDecision;
                   Prelude.False ->
                    TargetStrengtheningDerivedAcceptanceDecision};
                 Prelude.False -> TargetStrengtheningDerivedStatementDecision};
               Prelude.False -> TargetStrengtheningDerivedSubjectDecision};
             Prelude.False -> TargetStrengtheningDerivedIntroducerDecision};
           Prelude.False -> TargetStrengtheningDerivedRevisionDecision};
         Prelude.False -> TargetStrengtheningDerivedRequiredDecision};
       Prelude.False -> TargetStrengtheningSourceAssuranceDecision};
     Prelude.False -> TargetStrengtheningIntroducerDecision};
   Prelude.False -> TargetStrengtheningCoverageDecision}

data StagingEffectDecision =
   StagingEffectAcceptedDecision
 | StagingEffectCoverageDecision
 | StagingEffectRequirementDecision
 | StagingEffectEffectDecision
 | StagingEffectAuthorityDecision
 | StagingEffectFailureDecision
 | StagingEffectTransferDecision
 | StagingEffectCostDecision
 | StagingEffectBytesDecision
 | StagingEffectFrequencyDecision

decideStagingEffectByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                              StagingEffectDecision
decideStagingEffectByFacts coverageExact requirementIdentityPresent effectIdentityPresent authorityAccountPresent failureAccountValid subjectTransferPresent costIdentityPresent bytesCopiedAccounted frequencyAccounted =
  case coverageExact of {
   Prelude.True ->
    case requirementIdentityPresent of {
     Prelude.True ->
      case effectIdentityPresent of {
       Prelude.True ->
        case authorityAccountPresent of {
         Prelude.True ->
          case failureAccountValid of {
           Prelude.True ->
            case subjectTransferPresent of {
             Prelude.True ->
              case costIdentityPresent of {
               Prelude.True ->
                case bytesCopiedAccounted of {
                 Prelude.True ->
                  case frequencyAccounted of {
                   Prelude.True -> StagingEffectAcceptedDecision;
                   Prelude.False -> StagingEffectFrequencyDecision};
                 Prelude.False -> StagingEffectBytesDecision};
               Prelude.False -> StagingEffectCostDecision};
             Prelude.False -> StagingEffectTransferDecision};
           Prelude.False -> StagingEffectFailureDecision};
         Prelude.False -> StagingEffectAuthorityDecision};
       Prelude.False -> StagingEffectEffectDecision};
     Prelude.False -> StagingEffectRequirementDecision};
   Prelude.False -> StagingEffectCoverageDecision}

data NextStageExportDecision =
   NextStageExportAcceptedDecision
 | NextStageExportCoverageDecision
 | NextStageExportRevisionDecision
 | NextStageExportSourceDecision
 | NextStageExportFactDecision
 | NextStageExportFolkloreDecision
 | NextStageExportAcceptanceDecision
 | NextStageExportScopeDecision

decideNextStageExportByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool -> Prelude.Bool ->
                                Prelude.Bool -> Prelude.Bool ->
                                NextStageExportDecision
decideNextStageExportByFacts coverageExact revisionPresent sourceRefsPresent requiredFactPresent notFolkloreOnly acceptanceRulePresent validityScopePresent =
  case coverageExact of {
   Prelude.True ->
    case revisionPresent of {
     Prelude.True ->
      case sourceRefsPresent of {
       Prelude.True ->
        case requiredFactPresent of {
         Prelude.True ->
          case notFolkloreOnly of {
           Prelude.True ->
            case acceptanceRulePresent of {
             Prelude.True ->
              case validityScopePresent of {
               Prelude.True -> NextStageExportAcceptedDecision;
               Prelude.False -> NextStageExportScopeDecision};
             Prelude.False -> NextStageExportAcceptanceDecision};
           Prelude.False -> NextStageExportFolkloreDecision};
         Prelude.False -> NextStageExportFactDecision};
       Prelude.False -> NextStageExportSourceDecision};
     Prelude.False -> NextStageExportRevisionDecision};
   Prelude.False -> NextStageExportCoverageDecision}

data SystemsRealizationEffectsDecision =
   SystemsRealizationEffectsAcceptedDecision
 | SystemsRealizationEffectsStageClosureDecision
 | SystemsRealizationEffectsStrengtheningDecision
 | SystemsRealizationEffectsStagingDecision
 | SystemsRealizationEffectsNextStageDecision

decideSystemsRealizationEffectsByFacts :: Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool -> Prelude.Bool ->
                                          SystemsRealizationEffectsDecision
decideSystemsRealizationEffectsByFacts stageClosureAccepted strengtheningAccepted stagingAccepted nextStageAccepted =
  case stageClosureAccepted of {
   Prelude.True ->
    case strengtheningAccepted of {
     Prelude.True ->
      case stagingAccepted of {
       Prelude.True ->
        case nextStageAccepted of {
         Prelude.True -> SystemsRealizationEffectsAcceptedDecision;
         Prelude.False -> SystemsRealizationEffectsNextStageDecision};
       Prelude.False -> SystemsRealizationEffectsStagingDecision};
     Prelude.False -> SystemsRealizationEffectsStrengtheningDecision};
   Prelude.False -> SystemsRealizationEffectsStageClosureDecision}

