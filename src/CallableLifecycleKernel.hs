module CallableLifecycleKernel where

import qualified Prelude

data CallablePreserveDecision =
   CallablePreserveAccepted
 | CallablePreserveResidueMismatch
 | CallablePreserveProducedSuccessor

decideCallablePreserve :: Prelude.Bool -> Prelude.Bool ->
                          CallablePreserveDecision
decideCallablePreserve residueMatches successorAbsent =
  case residueMatches of {
   Prelude.True ->
    case successorAbsent of {
     Prelude.True -> CallablePreserveAccepted;
     Prelude.False -> CallablePreserveProducedSuccessor};
   Prelude.False -> CallablePreserveResidueMismatch}

data CallableConsumeDecision =
   CallableConsumeAccepted
 | CallableConsumeRetainedResidue
 | CallableConsumeProducedSuccessor

decideCallableConsume :: Prelude.Bool -> Prelude.Bool ->
                         CallableConsumeDecision
decideCallableConsume residueEmpty successorAbsent =
  case residueEmpty of {
   Prelude.True ->
    case successorAbsent of {
     Prelude.True -> CallableConsumeAccepted;
     Prelude.False -> CallableConsumeProducedSuccessor};
   Prelude.False -> CallableConsumeRetainedResidue}

data CallableReplaceDecision =
   CallableReplaceAccepted
 | CallableReplaceRetainedResidue
 | CallableReplaceMissingSuccessor
 | CallableReplaceReusedPredecessor
 | CallableReplaceSuccessorAlreadyAvailable
 | CallableReplaceInterfaceMismatch
 | CallableReplaceStateMismatch

decideCallableReplace :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                         Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                         CallableReplaceDecision
decideCallableReplace residueEmpty successorPresent successorDistinct successorFresh interfaceMatches stateMatches =
  case residueEmpty of {
   Prelude.True ->
    case successorPresent of {
     Prelude.True ->
      case successorDistinct of {
       Prelude.True ->
        case successorFresh of {
         Prelude.True ->
          case interfaceMatches of {
           Prelude.True ->
            case stateMatches of {
             Prelude.True -> CallableReplaceAccepted;
             Prelude.False -> CallableReplaceStateMismatch};
           Prelude.False -> CallableReplaceInterfaceMismatch};
         Prelude.False -> CallableReplaceSuccessorAlreadyAvailable};
       Prelude.False -> CallableReplaceReusedPredecessor};
     Prelude.False -> CallableReplaceMissingSuccessor};
   Prelude.False -> CallableReplaceRetainedResidue}

