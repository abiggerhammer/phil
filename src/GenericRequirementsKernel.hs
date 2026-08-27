module GenericRequirementsKernel where

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

negb :: Prelude.Bool -> Prelude.Bool
negb b =
  case b of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

data GenericStructuralRequirements =
   MkRequirements Prelude.Bool Prelude.Bool

requiresWeakening :: GenericStructuralRequirements -> Prelude.Bool
requiresWeakening g =
  case g of {
   MkRequirements requiresWeakening0 _ -> requiresWeakening0}

requiresContraction :: GenericStructuralRequirements -> Prelude.Bool
requiresContraction g =
  case g of {
   MkRequirements _ requiresContraction0 -> requiresContraction0}

boolImplies :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
boolImplies required available =
  orb (negb required) available

requirementsCover :: GenericStructuralRequirements ->
                     GenericStructuralRequirements -> Prelude.Bool
requirementsCover published induced =
  andb
    (boolImplies (requiresWeakening induced) (requiresWeakening published))
    (boolImplies (requiresContraction induced)
      (requiresContraction published))

data GenericRequirementsCoverageDecision =
   GenericRequirementsCoverageAccepted
 | GenericRequirementsCoverageMissingWeakening
 | GenericRequirementsCoverageMissingContraction

decideGenericRequirementsCoverage :: GenericStructuralRequirements ->
                                     GenericStructuralRequirements ->
                                     GenericRequirementsCoverageDecision
decideGenericRequirementsCoverage published induced =
  case andb (requiresWeakening induced) (negb (requiresWeakening published)) of {
   Prelude.True -> GenericRequirementsCoverageMissingWeakening;
   Prelude.False ->
    case andb (requiresContraction induced)
           (negb (requiresContraction published)) of {
     Prelude.True -> GenericRequirementsCoverageMissingContraction;
     Prelude.False -> GenericRequirementsCoverageAccepted}}

