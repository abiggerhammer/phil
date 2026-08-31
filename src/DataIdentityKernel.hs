module DataIdentityKernel where

import qualified Prelude

data DataIdentityDecision =
   DataIdentityAccepted
 | DataIdentityRejected

decideDataIdentityByFact :: Prelude.Bool -> DataIdentityDecision
decideDataIdentityByFact resolvedIdentityMatches =
  case resolvedIdentityMatches of {
   Prelude.True -> DataIdentityAccepted;
   Prelude.False -> DataIdentityRejected}

data DataOperationDecision =
   DataOperationAccepted
 | DataOperationRejected

decideDataOperationByFact :: Prelude.Bool -> DataOperationDecision
decideDataOperationByFact operationExplicitlyGranted =
  case operationExplicitlyGranted of {
   Prelude.True -> DataOperationAccepted;
   Prelude.False -> DataOperationRejected}

decideDataOperationAfterIdentityByFacts :: Prelude.Bool -> Prelude.Bool ->
                                           DataOperationDecision
decideDataOperationAfterIdentityByFacts _ =
  decideDataOperationByFact

