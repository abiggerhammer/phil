module RuntimeCarrierKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideExactCarrierBindingByFacts :: Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool -> Prelude.Bool
decideExactCarrierBindingByFacts bindingExact requiredUse carrierKnown dispositionCovered obligationExact siteRevisionExact siteEvidenceExact siteCostExact establishedAtSite claimAtSite processExact executionCovered runtimeAuthorityAccepted =
  andb bindingExact
    (andb requiredUse
      (andb carrierKnown
        (andb dispositionCovered
          (andb obligationExact
            (andb siteRevisionExact
              (andb siteEvidenceExact
                (andb siteCostExact
                  (andb establishedAtSite
                    (andb claimAtSite
                      (andb processExact
                        (andb executionCovered runtimeAuthorityAccepted)))))))))))

decideCoveredCarrierUseByFacts :: Prelude.Bool -> Prelude.Bool
decideCoveredCarrierUseByFacts exactBinding =
  exactBinding

decideExplicitBoundaryCarrierUseByFacts :: Prelude.Bool -> Prelude.Bool
decideExplicitBoundaryCarrierUseByFacts boundaryNonzero =
  boundaryNonzero

decidePreservedCarrierTransitionByFacts :: Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool -> Prelude.Bool
decidePreservedCarrierTransitionByFacts carrierKnown obligationExact processExact fromCovered toCovered =
  andb carrierKnown
    (andb obligationExact (andb processExact (andb fromCovered toCovered)))

decideReplacedCarrierTransitionByFacts :: Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool
decideReplacedCarrierTransitionByFacts priorKnown nextKnown obligationPriorExact obligationNextExact processPriorExact processNextExact fromCovered toCovered =
  andb priorKnown
    (andb nextKnown
      (andb obligationPriorExact
        (andb obligationNextExact
          (andb processPriorExact
            (andb processNextExact (andb fromCovered toCovered))))))

decideClosedCarrierTransitionByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool
decideClosedCarrierTransitionByFacts carrierKnown obligationExact processExact fromCovered destinationNotRuntimeBound =
  andb carrierKnown
    (andb obligationExact
      (andb processExact (andb fromCovered destinationNotRuntimeBound)))

