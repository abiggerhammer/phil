module StorageAllocationFailureKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideStorageFailureRealizationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool
decideStorageFailureRealizationByFacts =
  andb

decideStorageFailureCannotFailByFacts :: Prelude.Bool
decideStorageFailureCannotFailByFacts =
  Prelude.True

decideStorageFailureMapsToSourceByFacts :: Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool
decideStorageFailureMapsToSourceByFacts =
  andb

decideStorageFailureProvedUnreachableByFacts :: Prelude.Bool -> Prelude.Bool
decideStorageFailureProvedUnreachableByFacts evidenceIdentityValid =
  evidenceIdentityValid

decideStorageFailureAssumptionByFacts :: Prelude.Bool -> Prelude.Bool
decideStorageFailureAssumptionByFacts assumptionIdentityValid =
  assumptionIdentityValid

decideStorageFailureDeploymentRequirementByFacts :: Prelude.Bool ->
                                                    Prelude.Bool
decideStorageFailureDeploymentRequirementByFacts requirementIdentityValid =
  requirementIdentityValid

decideStorageFailureUnaccountedByFacts :: Prelude.Bool
decideStorageFailureUnaccountedByFacts =
  Prelude.False

