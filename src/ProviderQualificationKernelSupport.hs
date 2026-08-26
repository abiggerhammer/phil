module ProviderQualificationKernelSupport where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

sameKeyDomainb :: (a1 -> a1 -> Prelude.Bool) -> ([] ((,) a1 a2)) -> ([]
                  ((,) a1 a3)) -> Prelude.Bool
sameKeyDomainb eqKey first second =
  case first of {
   [] -> case second of {
          [] -> Prelude.True;
          (:) _ _ -> Prelude.False};
   (:) p firstRest ->
    case p of {
     (,) firstKey _ ->
      case second of {
       [] -> Prelude.False;
       (:) p0 secondRest ->
        case p0 of {
         (,) secondKey _ ->
          andb (eqKey firstKey secondKey)
            (sameKeyDomainb eqKey firstRest secondRest)}}}}

lookupAssoc :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] ((,) a1 a2)) ->
               Prelude.Maybe a2
lookupAssoc eqKey key entries =
  case entries of {
   [] -> Prelude.Nothing;
   (:) p rest ->
    case p of {
     (,) entryKey value ->
      case eqKey key entryKey of {
       Prelude.True -> Prelude.Just value;
       Prelude.False -> lookupAssoc eqKey key rest}}}

allFiniteb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
allFiniteb predicate values =
  case values of {
   [] -> Prelude.True;
   (:) value rest -> andb (predicate value) (allFiniteb predicate rest)}

