module CallableRecursionKernel where

import qualified Prelude

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> b2}

keyOccursb :: (a2 -> a2 -> Prelude.Bool) -> (a1 -> a2) -> a2 -> ([] a1) ->
              Prelude.Bool
keyOccursb eqKey keyOf key definitions =
  case definitions of {
   [] -> Prelude.False;
   (:) definition rest ->
    orb (eqKey key (keyOf definition)) (keyOccursb eqKey keyOf key rest)}

stabilizePublic :: (a2 -> a2 -> Prelude.Bool) -> (a1 -> a2) -> (a1 -> a3) ->
                   ([] a1) -> Prelude.Maybe ([] ((,) a2 a3))
stabilizePublic eqKey keyOf surfaceOf definitions =
  case definitions of {
   [] -> Prelude.Just [];
   (:) definition rest ->
    case keyOccursb eqKey keyOf (keyOf definition) rest of {
     Prelude.True -> Prelude.Nothing;
     Prelude.False ->
      case stabilizePublic eqKey keyOf surfaceOf rest of {
       Prelude.Just environment -> Prelude.Just ((:) ((,) (keyOf definition)
        (surfaceOf definition)) environment);
       Prelude.Nothing -> Prelude.Nothing}}}

lookupPublic :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] ((,) a1 a2)) ->
                Prelude.Maybe a2
lookupPublic eqKey key environment =
  case environment of {
   [] -> Prelude.Nothing;
   (:) p rest ->
    case p of {
     (,) entryKey surface ->
      case eqKey key entryKey of {
       Prelude.True -> Prelude.Just surface;
       Prelude.False -> lookupPublic eqKey key rest}}}

data RecursiveLookupDecision surface =
   RecursiveLookupAccepted surface
 | RecursiveLookupUnknown
 | RecursiveLookupRevisionMismatch surface

decideRecursiveLookup :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (a2 ->
                         Prelude.Bool) -> ([] ((,) a1 a2)) ->
                         RecursiveLookupDecision a2
decideRecursiveLookup eqKey key revisionMatches environment =
  case lookupPublic eqKey key environment of {
   Prelude.Just surface ->
    case revisionMatches surface of {
     Prelude.True -> RecursiveLookupAccepted surface;
     Prelude.False -> RecursiveLookupRevisionMismatch surface};
   Prelude.Nothing -> RecursiveLookupUnknown}

