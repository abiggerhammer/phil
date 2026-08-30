module BoundaryProgressionKernel where

import qualified Prelude

data EmissionDisposition =
   InvalidEmissionExtent
 | PartialEmission
 | CompleteEmission
 | EmissionPastDeclaredFrame

data ReceiveProgressionDecision =
   ReceiveProgressionDecisionAccepted
 | ReceiveMappingGrammarMismatchDecision
 | ReceiveMappingValueMismatchDecision
 | UnderlyingReceiveRejectedDecision

decideReceiveProgressionByFacts :: Prelude.Bool -> Prelude.Bool ->
                                   Prelude.Bool -> ReceiveProgressionDecision
decideReceiveProgressionByFacts grammarMatches valueMatches underlyingAccepted =
  case grammarMatches of {
   Prelude.True ->
    case valueMatches of {
     Prelude.True ->
      case underlyingAccepted of {
       Prelude.True -> ReceiveProgressionDecisionAccepted;
       Prelude.False -> UnderlyingReceiveRejectedDecision};
     Prelude.False -> ReceiveMappingValueMismatchDecision};
   Prelude.False -> ReceiveMappingGrammarMismatchDecision}

data CompleteEmissionDecision =
   CompleteEmissionDecisionAccepted
 | InvalidEmissionExtentDecision
 | PartialEmissionDecision
 | EmissionPastDeclaredFrameDecision

decideEmissionDisposition :: EmissionDisposition -> CompleteEmissionDecision
decideEmissionDisposition disposition =
  case disposition of {
   InvalidEmissionExtent -> InvalidEmissionExtentDecision;
   PartialEmission -> PartialEmissionDecision;
   CompleteEmission -> CompleteEmissionDecisionAccepted;
   EmissionPastDeclaredFrame -> EmissionPastDeclaredFrameDecision}

data CompleteEmissionPlan representation owner =
   MkCompleteEmissionPlan representation owner

planCompleteEmission :: a1 -> a2 -> CompleteEmissionPlan a1 a2
planCompleteEmission representationId ownerId =
  MkCompleteEmissionPlan representationId ownerId

data SendProgressionDecision =
   SendProgressionDecisionAccepted
 | SendEmissionRepresentationMismatchDecision
 | SendEmissionOwnerMismatchDecision
 | UnderlyingSendRejectedDecision

decideSendProgressionByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> SendProgressionDecision
decideSendProgressionByFacts representationMatches ownerMatches underlyingAccepted =
  case representationMatches of {
   Prelude.True ->
    case ownerMatches of {
     Prelude.True ->
      case underlyingAccepted of {
       Prelude.True -> SendProgressionDecisionAccepted;
       Prelude.False -> UnderlyingSendRejectedDecision};
     Prelude.False -> SendEmissionOwnerMismatchDecision};
   Prelude.False -> SendEmissionRepresentationMismatchDecision}

