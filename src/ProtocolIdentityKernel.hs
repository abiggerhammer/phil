module ProtocolIdentityKernel where

import qualified Prelude

data ProtocolContractDecision =
   ProtocolContractAccepted
 | ProtocolContractInstanceMismatchDecision
 | ProtocolContractRoleMismatchDecision
 | ProtocolContractSessionMismatchDecision

decideProtocolContractByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                 -> ProtocolContractDecision
decideProtocolContractByFacts instanceMatches roleMatches sessionMatches =
  case instanceMatches of {
   Prelude.True ->
    case roleMatches of {
     Prelude.True ->
      case sessionMatches of {
       Prelude.True -> ProtocolContractAccepted;
       Prelude.False -> ProtocolContractSessionMismatchDecision};
     Prelude.False -> ProtocolContractRoleMismatchDecision};
   Prelude.False -> ProtocolContractInstanceMismatchDecision}

data ProtocolActionDecision =
   ProtocolActionAccepted
 | ProtocolActionInstanceMismatchDecision
 | ProtocolActionRoleMismatchDecision
 | ProtocolActionLocalStateRejectedDecision

decideProtocolActionByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                               -> ProtocolActionDecision
decideProtocolActionByFacts instanceMatches roleMatches localStateAllows =
  case instanceMatches of {
   Prelude.True ->
    case roleMatches of {
     Prelude.True ->
      case localStateAllows of {
       Prelude.True -> ProtocolActionAccepted;
       Prelude.False -> ProtocolActionLocalStateRejectedDecision};
     Prelude.False -> ProtocolActionRoleMismatchDecision};
   Prelude.False -> ProtocolActionInstanceMismatchDecision}

data ProtocolContractPlan instance0 roleKeyType session =
   MkProtocolContractPlan instance0 roleKeyType session

planProtocolContract :: a1 -> a2 -> a3 -> ProtocolContractPlan a1 a2 a3
planProtocolContract instanceRevision roleKey localSession =
  MkProtocolContractPlan instanceRevision roleKey localSession

