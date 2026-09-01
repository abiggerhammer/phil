module BoundarySubjectKernel where

import qualified Prelude

data BoundarySubjectTransferDecision =
   BoundarySubjectTransferAcceptedDecision
 | BoundarySubjectRuntimeCoincidenceDecision
 | BoundarySubjectTransportKindDecision
 | BoundarySubjectCopyRevisionDecision
 | BoundarySubjectByteEqualityDecision
 | BoundarySubjectTransferLawDecision
 | BoundarySubjectEvidenceReferenceDecision
 | BoundarySubjectValidityScopeDecision

decideBoundarySubjectTransferByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool ->
                                        BoundarySubjectTransferDecision
decideBoundarySubjectTransferByFacts checkedCandidate kindIsCopy copyRevisionPresent byteEqualityPresent transferLawPresent evidenceReferenceExact validityScopePresent =
  case checkedCandidate of {
   Prelude.True ->
    case kindIsCopy of {
     Prelude.True ->
      case copyRevisionPresent of {
       Prelude.True ->
        case byteEqualityPresent of {
         Prelude.True ->
          case transferLawPresent of {
           Prelude.True ->
            case evidenceReferenceExact of {
             Prelude.True ->
              case validityScopePresent of {
               Prelude.True -> BoundarySubjectTransferAcceptedDecision;
               Prelude.False -> BoundarySubjectValidityScopeDecision};
             Prelude.False -> BoundarySubjectEvidenceReferenceDecision};
           Prelude.False -> BoundarySubjectTransferLawDecision};
         Prelude.False -> BoundarySubjectByteEqualityDecision};
       Prelude.False -> BoundarySubjectCopyRevisionDecision};
     Prelude.False -> BoundarySubjectTransportKindDecision};
   Prelude.False -> BoundarySubjectRuntimeCoincidenceDecision}

data ZeroCopyRealizationDecision =
   ZeroCopyRealizationAcceptedDecision
 | ZeroCopyPointerReinterpretationDecision
 | ZeroCopyStageRevisionDecision
 | ZeroCopyBoundaryRepresentationDecision
 | ZeroCopyGrammarDecision
 | ZeroCopyValueTypeDecision
 | ZeroCopySourceSemanticLayoutDecision
 | ZeroCopyConcreteMemoryLayoutDecision
 | ZeroCopyEndianAlignmentPaddingTaggingDecision
 | ZeroCopyLifetimeRulesDecision
 | ZeroCopyOwnershipRulesDecision
 | ZeroCopyDeviceStorageConstraintsDecision
 | ZeroCopyTargetAssumptionsCarriersDecision

decideZeroCopyRealizationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    ZeroCopyRealizationDecision
decideZeroCopyRealizationByFacts checkedRealization stageExact boundaryRepresentationPresent grammarPresent valueTypePresent sourceSemanticLayoutPresent concreteMemoryLayoutPresent endianAlignmentPaddingTaggingPresent lifetimeRulesPresent ownershipRulesPresent deviceStorageConstraintsPresent targetAssumptionsCarriersPresent =
  case checkedRealization of {
   Prelude.True ->
    case stageExact of {
     Prelude.True ->
      case boundaryRepresentationPresent of {
       Prelude.True ->
        case grammarPresent of {
         Prelude.True ->
          case valueTypePresent of {
           Prelude.True ->
            case sourceSemanticLayoutPresent of {
             Prelude.True ->
              case concreteMemoryLayoutPresent of {
               Prelude.True ->
                case endianAlignmentPaddingTaggingPresent of {
                 Prelude.True ->
                  case lifetimeRulesPresent of {
                   Prelude.True ->
                    case ownershipRulesPresent of {
                     Prelude.True ->
                      case deviceStorageConstraintsPresent of {
                       Prelude.True ->
                        case targetAssumptionsCarriersPresent of {
                         Prelude.True -> ZeroCopyRealizationAcceptedDecision;
                         Prelude.False ->
                          ZeroCopyTargetAssumptionsCarriersDecision};
                       Prelude.False ->
                        ZeroCopyDeviceStorageConstraintsDecision};
                     Prelude.False -> ZeroCopyOwnershipRulesDecision};
                   Prelude.False -> ZeroCopyLifetimeRulesDecision};
                 Prelude.False ->
                  ZeroCopyEndianAlignmentPaddingTaggingDecision};
               Prelude.False -> ZeroCopyConcreteMemoryLayoutDecision};
             Prelude.False -> ZeroCopySourceSemanticLayoutDecision};
           Prelude.False -> ZeroCopyValueTypeDecision};
         Prelude.False -> ZeroCopyGrammarDecision};
       Prelude.False -> ZeroCopyBoundaryRepresentationDecision};
     Prelude.False -> ZeroCopyStageRevisionDecision};
   Prelude.False -> ZeroCopyPointerReinterpretationDecision}

