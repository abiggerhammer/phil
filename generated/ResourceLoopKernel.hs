module ResourceLoopKernel where

import qualified Prelude

data LoopProjectionDecision =
   LoopProjectionAcceptedDecision
 | LoopProjectionKindDecision
 | LoopProjectionResourceDecision
 | LoopProjectionSlotDomainDecision
 | LoopProjectionRequirementDecision

decideLoopProjectionByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                               -> Prelude.Bool -> LoopProjectionDecision
decideLoopProjectionByFacts kindMatches resourceProjectionAccepted slotDomainExact requirementsExact =
  case kindMatches of {
   Prelude.True ->
    case resourceProjectionAccepted of {
     Prelude.True ->
      case slotDomainExact of {
       Prelude.True ->
        case requirementsExact of {
         Prelude.True -> LoopProjectionAcceptedDecision;
         Prelude.False -> LoopProjectionRequirementDecision};
       Prelude.False -> LoopProjectionSlotDomainDecision};
     Prelude.False -> LoopProjectionResourceDecision};
   Prelude.False -> LoopProjectionKindDecision}

data StateTransportDecision =
   StateTransportAcceptedDecision
 | StateTransportExplicitEvidenceDecision

decideStateTransportByFacts :: Prelude.Bool -> Prelude.Bool ->
                               StateTransportDecision
decideStateTransportByFacts definitionallyEqual explicitEvidenceAccepted =
  case definitionallyEqual of {
   Prelude.True -> StateTransportAcceptedDecision;
   Prelude.False ->
    case explicitEvidenceAccepted of {
     Prelude.True -> StateTransportAcceptedDecision;
     Prelude.False -> StateTransportExplicitEvidenceDecision}}

