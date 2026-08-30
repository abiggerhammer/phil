module BoundaryRepresentationKernel where

import qualified Prelude

data BoundaryDirection =
   ReceiveOnly
 | SendOnly
 | Bidirectional

data BoundaryUse =
   InboundUse
 | OutboundUse

data BoundaryDirectionError =
   ReceiveOnlyCannotEncode
 | SendOnlyCannotAcceptInbound

data BoundaryDirectionResult =
   BoundaryUseAccepted
 | BoundaryUseRejected BoundaryDirectionError

checkBoundaryUse :: BoundaryDirection -> BoundaryUse ->
                    BoundaryDirectionResult
checkBoundaryUse direction use =
  case direction of {
   ReceiveOnly ->
    case use of {
     InboundUse -> BoundaryUseAccepted;
     OutboundUse -> BoundaryUseRejected ReceiveOnlyCannotEncode};
   SendOnly ->
    case use of {
     InboundUse -> BoundaryUseRejected SendOnlyCannotAcceptInbound;
     OutboundUse -> BoundaryUseAccepted};
   Bidirectional -> BoundaryUseAccepted}

data BoundaryMappingDecision =
   BoundaryMappingDecisionAccepted
 | BoundaryRepresentationMismatchDecision
 | BoundaryGrammarMismatchDecision
 | BoundaryValueTypeMismatchDecision
 | RecognizedGrammarMismatchDecision
 | RecognizedValueMismatchDecision
 | BoundaryMappingRejectedDecision

decideBoundaryMappingByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool -> Prelude.Bool ->
                                Prelude.Bool -> BoundaryMappingDecision
decideBoundaryMappingByFacts representationMatches grammarMatches valueTypeMatches recognizedGrammarMatches recognizedValueMatches dispositionAccepted =
  case representationMatches of {
   Prelude.True ->
    case grammarMatches of {
     Prelude.True ->
      case valueTypeMatches of {
       Prelude.True ->
        case recognizedGrammarMatches of {
         Prelude.True ->
          case recognizedValueMatches of {
           Prelude.True ->
            case dispositionAccepted of {
             Prelude.True -> BoundaryMappingDecisionAccepted;
             Prelude.False -> BoundaryMappingRejectedDecision};
           Prelude.False -> RecognizedValueMismatchDecision};
         Prelude.False -> RecognizedGrammarMismatchDecision};
       Prelude.False -> BoundaryValueTypeMismatchDecision};
     Prelude.False -> BoundaryGrammarMismatchDecision};
   Prelude.False -> BoundaryRepresentationMismatchDecision}

data BoundaryCorrespondencePlan representation grammar valueType value =
   MkBoundaryCorrespondencePlan representation grammar valueType value 
 value

planBoundaryCorrespondence :: a1 -> a2 -> a3 -> a4 -> a4 ->
                              BoundaryCorrespondencePlan a1 a2 a3 a4
planBoundaryCorrespondence representationId grammarId valueTypeId grammarValue semanticValue =
  MkBoundaryCorrespondencePlan representationId grammarId valueTypeId
    grammarValue semanticValue

decideBoundaryUse :: BoundaryDirection -> BoundaryUse ->
                     BoundaryDirectionResult
decideBoundaryUse =
  checkBoundaryUse
