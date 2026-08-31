module ProtocolProgressionGuardKernel where

import qualified Prelude

data ProtocolContinuationDecision =
   ProtocolContinuationAccepted
 | ProtocolContinuationPredecessorMissingDecision
 | ProtocolContinuationSameNameDecision
 | ProtocolContinuationSuccessorOccupiedDecision

decideProtocolContinuationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool ->
                                     ProtocolContinuationDecision
decideProtocolContinuationByFacts predecessorLive namesDistinct successorFresh =
  case predecessorLive of {
   Prelude.True ->
    case namesDistinct of {
     Prelude.True ->
      case successorFresh of {
       Prelude.True -> ProtocolContinuationAccepted;
       Prelude.False -> ProtocolContinuationSuccessorOccupiedDecision};
     Prelude.False -> ProtocolContinuationSameNameDecision};
   Prelude.False -> ProtocolContinuationPredecessorMissingDecision}

data ProtocolCloseDecision =
   ProtocolCloseAccepted
 | ProtocolClosePredecessorMissingDecision

decideProtocolCloseByFact :: Prelude.Bool -> ProtocolCloseDecision
decideProtocolCloseByFact predecessorLive =
  case predecessorLive of {
   Prelude.True -> ProtocolCloseAccepted;
   Prelude.False -> ProtocolClosePredecessorMissingDecision}

data ProtocolSuccessorContractPlan instanceType roleType sessionType =
   MkProtocolSuccessorContractPlan instanceType roleType sessionType

planProtocolSuccessorContract :: a1 -> a2 -> a3 ->
                                 ProtocolSuccessorContractPlan a1 a2 
                                 a3
planProtocolSuccessorContract instanceRevision role successorSession =
  MkProtocolSuccessorContractPlan instanceRevision role successorSession

data ProtocolGuardListDecision =
   ProtocolGuardListAccepted
 | ProtocolGuardListDuplicateDecision

decideProtocolGuardListByFact :: Prelude.Bool -> ProtocolGuardListDecision
decideProtocolGuardListByFact guardsUnique =
  case guardsUnique of {
   Prelude.True -> ProtocolGuardListAccepted;
   Prelude.False -> ProtocolGuardListDuplicateDecision}

data ProtocolGuardRequirementDecision =
   ProtocolGuardRequirementAccepted
 | ProtocolGuardRevisionMissingDecision
 | ProtocolGuardRevisionNotCertifiedDecision

decideProtocolGuardRequirementByFacts :: Prelude.Bool -> Prelude.Bool ->
                                         ProtocolGuardRequirementDecision
decideProtocolGuardRequirementByFacts revisionPresent revisionCertified =
  case revisionPresent of {
   Prelude.True ->
    case revisionCertified of {
     Prelude.True -> ProtocolGuardRequirementAccepted;
     Prelude.False -> ProtocolGuardRevisionNotCertifiedDecision};
   Prelude.False -> ProtocolGuardRevisionMissingDecision}

