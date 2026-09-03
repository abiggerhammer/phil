module ResourceObligationKernel where

import qualified Prelude

data PendingObligationDecision =
   PendingObligationAcceptedDecision
 | PendingObligationLostDecision

decidePendingObligationReconvergenceByFacts :: Prelude.Bool -> Prelude.Bool
                                               -> PendingObligationDecision
decidePendingObligationReconvergenceByFacts pendingBefore pendingAfter =
  case pendingBefore of {
   Prelude.True ->
    case pendingAfter of {
     Prelude.True -> PendingObligationAcceptedDecision;
     Prelude.False -> PendingObligationLostDecision};
   Prelude.False -> PendingObligationAcceptedDecision}

