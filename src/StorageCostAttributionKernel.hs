module StorageCostAttributionKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> b2}

decideStorageCostSubjectExactByFacts :: Prelude.Bool -> Prelude.Bool
decideStorageCostSubjectExactByFacts subjectExact =
  subjectExact

decideStorageCostPhysicalDomainExactByFacts :: Prelude.Bool -> Prelude.Bool
decideStorageCostPhysicalDomainExactByFacts physicalDomainExact =
  physicalDomainExact

decideAttributableStorageCostByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool
decideAttributableStorageCostByFacts allocationCountPresent peakLiveMemoryPresent bytesCopiedPresent residencyRefPresent cleanupRefPresent =
  orb allocationCountPresent
    (orb peakLiveMemoryPresent
      (orb bytesCopiedPresent (orb residencyRefPresent cleanupRefPresent)))

decideStorageCostLineageValidByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool
decideStorageCostLineageValidByFacts subjectExact physicalDomainExact attributableCost =
  andb subjectExact (andb physicalDomainExact attributableCost)

decideStorageRuntimeCostBindingByFacts :: Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool -> Prelude.Bool
decideStorageRuntimeCostBindingByFacts contributionInCharge classExact shapeExact =
  andb contributionInCharge (andb classExact shapeExact)

decideCertifiedStorageCostAttributionByFacts :: Prelude.Bool -> Prelude.Bool
                                                -> Prelude.Bool ->
                                                Prelude.Bool
decideCertifiedStorageCostAttributionByFacts realizationValid runtimeGraphValid lineageValid =
  andb realizationValid (andb runtimeGraphValid lineageValid)

