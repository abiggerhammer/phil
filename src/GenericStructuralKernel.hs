module GenericStructuralKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

negb :: Prelude.Bool -> Prelude.Bool
negb b =
  case b of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

fold_left :: (a1 -> a2 -> a1) -> ([] a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   [] -> a0;
   (:) b l0 -> fold_left f l0 (f a0 b)}

data Mode =
   Unrestricted
 | Affine
 | Linear

data StructuralPermission =
   WeakeningPermission
 | ContractionPermission

data GenericStructuralUse =
   TransferGenericValue
 | DiscardGenericValue
 | DuplicateGenericValue

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

emptyRequirements :: GenericStructuralRequirements
emptyRequirements =
  MkRequirements Prelude.False Prelude.False

addStructuralUse :: GenericStructuralUse -> GenericStructuralRequirements ->
                    GenericStructuralRequirements
addStructuralUse use requirements =
  case use of {
   TransferGenericValue -> requirements;
   DiscardGenericValue -> MkRequirements Prelude.True
    (requiresContraction requirements);
   DuplicateGenericValue -> MkRequirements (requiresWeakening requirements)
    Prelude.True}

inferGenericStructuralRequirements :: ([] GenericStructuralUse) ->
                                      GenericStructuralRequirements
inferGenericStructuralRequirements uses =
  fold_left (\requirements use -> addStructuralUse use requirements) uses
    emptyRequirements

modeAllowsStructuralPermission :: Mode -> StructuralPermission ->
                                  Prelude.Bool
modeAllowsStructuralPermission mode permission =
  case mode of {
   Unrestricted -> Prelude.True;
   Affine ->
    case permission of {
     WeakeningPermission -> Prelude.True;
     ContractionPermission -> Prelude.False};
   Linear -> Prelude.False}

modeSatisfiesRequirements :: Mode -> GenericStructuralRequirements ->
                             Prelude.Bool
modeSatisfiesRequirements mode requirements =
  andb
    (case requiresWeakening requirements of {
      Prelude.True -> modeAllowsStructuralPermission mode WeakeningPermission;
      Prelude.False -> Prelude.True})
    (case requiresContraction requirements of {
      Prelude.True ->
       modeAllowsStructuralPermission mode ContractionPermission;
      Prelude.False -> Prelude.True})

data GenericStructuralActualDecision =
   GenericStructuralActualAccepted
 | GenericStructuralActualMissingWeakening
 | GenericStructuralActualMissingContraction

decideGenericStructuralActual :: Mode -> GenericStructuralRequirements ->
                                 GenericStructuralActualDecision
decideGenericStructuralActual mode requirements =
  case andb (requiresWeakening requirements)
         (negb (modeAllowsStructuralPermission mode WeakeningPermission)) of {
   Prelude.True -> GenericStructuralActualMissingWeakening;
   Prelude.False ->
    case andb (requiresContraction requirements)
           (negb (modeAllowsStructuralPermission mode ContractionPermission)) of {
     Prelude.True -> GenericStructuralActualMissingContraction;
     Prelude.False -> GenericStructuralActualAccepted}}

