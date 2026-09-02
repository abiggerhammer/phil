module SystemsRuntimeGraphKernel where

import qualified Prelude

data RuntimeClaimGraphDecision =
   RuntimeClaimGraphAcceptedDecision
 | RuntimeClaimGraphSiteVerificationDecision

decideRuntimeClaimGraphByFacts :: Prelude.Bool -> RuntimeClaimGraphDecision
decideRuntimeClaimGraphByFacts allSitesVerified =
  case allSitesVerified of {
   Prelude.True -> RuntimeClaimGraphAcceptedDecision;
   Prelude.False -> RuntimeClaimGraphSiteVerificationDecision}

data RuntimePrimitiveReuseDecision =
   RuntimePrimitiveReuseAcceptedDecision
 | RuntimePrimitiveReuseContributionIdentityDecision
 | RuntimePrimitiveReuseSymbolIdentityDecision

decideRuntimePrimitiveReuseByFacts :: Prelude.Bool -> Prelude.Bool ->
                                      RuntimePrimitiveReuseDecision
decideRuntimePrimitiveReuseByFacts contributionIdentifiesSite runtimeSymbolsVerified =
  case contributionIdentifiesSite of {
   Prelude.True ->
    case runtimeSymbolsVerified of {
     Prelude.True -> RuntimePrimitiveReuseAcceptedDecision;
     Prelude.False -> RuntimePrimitiveReuseSymbolIdentityDecision};
   Prelude.False -> RuntimePrimitiveReuseContributionIdentityDecision}

data RuntimeCostAttributionDecision =
   RuntimeCostAttributionAcceptedDecision
 | RuntimeCostAttributionClassDecision
 | RuntimeCostAttributionShapeDecision

decideRuntimeCostAttributionByFacts :: Prelude.Bool -> Prelude.Bool ->
                                       RuntimeCostAttributionDecision
decideRuntimeCostAttributionByFacts sharedChargeClassCompatible sharedChargeShapeCompatible =
  case sharedChargeClassCompatible of {
   Prelude.True ->
    case sharedChargeShapeCompatible of {
     Prelude.True -> RuntimeCostAttributionAcceptedDecision;
     Prelude.False -> RuntimeCostAttributionShapeDecision};
   Prelude.False -> RuntimeCostAttributionClassDecision}

data SystemsRuntimeGraphDecision =
   SystemsRuntimeGraphAcceptedDecision
 | SystemsRuntimeGraphClaimGraphDecision
 | SystemsRuntimeGraphPrimitiveReuseDecision
 | SystemsRuntimeGraphCostAttributionDecision

decideSystemsRuntimeGraphByFacts :: Prelude.Bool -> Prelude.Bool ->
                                    Prelude.Bool ->
                                    SystemsRuntimeGraphDecision
decideSystemsRuntimeGraphByFacts claimGraphAccepted primitiveReuseAccepted costAttributionAccepted =
  case claimGraphAccepted of {
   Prelude.True ->
    case primitiveReuseAccepted of {
     Prelude.True ->
      case costAttributionAccepted of {
       Prelude.True -> SystemsRuntimeGraphAcceptedDecision;
       Prelude.False -> SystemsRuntimeGraphCostAttributionDecision};
     Prelude.False -> SystemsRuntimeGraphPrimitiveReuseDecision};
   Prelude.False -> SystemsRuntimeGraphClaimGraphDecision}

