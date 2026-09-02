module ResourceJoinKernel where

import qualified Prelude

data ResourceProjectionDecision =
   ResourceProjectionAcceptedDecision
 | ResourceProjectionLinearCoverageDecision
 | ResourceProjectionInventedOwnerDecision
 | ResourceProjectionSubjectAdmissionDecision

decideResourceProjectionByFacts :: Prelude.Bool -> Prelude.Bool ->
                                   Prelude.Bool -> ResourceProjectionDecision
decideResourceProjectionByFacts allIncomingLinearExactlyOnceBound noInventedOwners allBoundSubjectsAdmissible =
  case allIncomingLinearExactlyOnceBound of {
   Prelude.True ->
    case noInventedOwners of {
     Prelude.True ->
      case allBoundSubjectsAdmissible of {
       Prelude.True -> ResourceProjectionAcceptedDecision;
       Prelude.False -> ResourceProjectionSubjectAdmissionDecision};
     Prelude.False -> ResourceProjectionInventedOwnerDecision};
   Prelude.False -> ResourceProjectionLinearCoverageDecision}

