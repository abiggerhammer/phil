module GenericInstantiationDomainKernel where

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

existsb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
existsb f l =
  case l of {
   [] -> Prelude.False;
   (:) a l0 -> orb (f a) (existsb f l0)}

keyIn :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] a1) -> Prelude.Bool
keyIn keyEqb needle haystack =
  existsb (keyEqb needle) haystack

keyListNoDupb :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
keyListNoDupb keyEqb keys =
  case keys of {
   [] -> Prelude.True;
   (:) key rest ->
    andb (negb (keyIn keyEqb key rest)) (keyListNoDupb keyEqb rest)}

allKeysInb :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> ([] a1) ->
              Prelude.Bool
allKeysInb keyEqb required available =
  case required of {
   [] -> Prelude.True;
   (:) key rest ->
    andb (keyIn keyEqb key available) (allKeysInb keyEqb rest available)}

exactKeyDomainb :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> ([] a1) ->
                   Prelude.Bool
exactKeyDomainb keyEqb requirements dispositionKeys =
  andb (keyListNoDupb keyEqb dispositionKeys)
    (andb (allKeysInb keyEqb requirements dispositionKeys)
      (allKeysInb keyEqb dispositionKeys requirements))

data GenericDispositionDomainDecision =
   GenericDispositionDomainAccepted
 | GenericDispositionDomainRejected

decideExactKeyDomain :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> ([] 
                        a1) -> GenericDispositionDomainDecision
decideExactKeyDomain keyEqb requirements dispositionKeys =
  case exactKeyDomainb keyEqb requirements dispositionKeys of {
   Prelude.True -> GenericDispositionDomainAccepted;
   Prelude.False -> GenericDispositionDomainRejected}
