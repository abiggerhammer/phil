module ProviderQualificationKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

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

type ContractOperationProjection contractOperation outcomeKey residue =
  (,) contractOperation ([] ((,) outcomeKey residue))

type ImplementationOperationProjection
  implementationOperation outcomeKey residue =
  (,) implementationOperation ([] ((,) outcomeKey residue))

type CorrespondenceProjection entryKey outcomeKey =
  (,) entryKey ([] ((,) outcomeKey outcomeKey))

decideOutcomeMapping :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                        Prelude.Bool) -> ([] ((,) a1 a2)) -> ([] ((,) a1 a2))
                        -> ((,) a1 a1) -> Prelude.Bool
decideOutcomeMapping eqOutcome residueEqual contractOutcomes implementationOutcomes mapping =
  let {implementationOutcome = fst mapping} in
  let {contractOutcome = snd mapping} in
  case lookupAssoc eqOutcome implementationOutcome implementationOutcomes of {
   Prelude.Just implementationResidue ->
    case lookupAssoc eqOutcome contractOutcome contractOutcomes of {
     Prelude.Just contractResidue ->
      residueEqual implementationResidue contractResidue;
     Prelude.Nothing -> Prelude.False};
   Prelude.Nothing -> Prelude.False}

decideOutcomeTraversal :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                          Prelude.Bool) -> ([] ((,) a1 a2)) -> ([]
                          ((,) a1 a2)) -> ([] ((,) a1 a1)) -> Prelude.Bool
decideOutcomeTraversal eqOutcome residueEqual contractOutcomes implementationOutcomes outcomeMappings =
  andb (sameKeyDomainb eqOutcome implementationOutcomes outcomeMappings)
    (allFiniteb
      (decideOutcomeMapping eqOutcome residueEqual contractOutcomes
        implementationOutcomes)
      outcomeMappings)

decideOperationTraversal :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                            Prelude.Bool) -> (a5 -> a5 -> Prelude.Bool) ->
                            (a3 -> a4 -> Prelude.Bool) -> ([]
                            ((,) a1
                            (ImplementationOperationProjection a4 a2 a5))) ->
                            (ContractOperationProjection a3 a2 a5) ->
                            (CorrespondenceProjection a1 a2) -> Prelude.Bool
decideOperationTraversal eqEntry eqOutcome residueEqual operationAccepts implementationEntries contractProjection correspondence =
  case lookupAssoc eqEntry (fst correspondence) implementationEntries of {
   Prelude.Just implementationProjection ->
    andb
      (operationAccepts (fst contractProjection)
        (fst implementationProjection))
      (decideOutcomeTraversal eqOutcome residueEqual (snd contractProjection)
        (snd implementationProjection) (snd correspondence));
   Prelude.Nothing -> Prelude.False}

decideOperationAt :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 -> Prelude.Bool)
                     -> (a3 -> a3 -> Prelude.Bool) -> (a6 -> a6 ->
                     Prelude.Bool) -> (a4 -> a5 -> Prelude.Bool) -> ([]
                     ((,) a1 (CorrespondenceProjection a2 a3))) -> ([]
                     ((,) a2 (ImplementationOperationProjection a5 a3 a6)))
                     -> ((,) a1 (ContractOperationProjection a4 a3 a6)) ->
                     Prelude.Bool
decideOperationAt eqOperation eqEntry eqOutcome residueEqual operationAccepts correspondences implementationEntries operation =
  case lookupAssoc eqOperation (fst operation) correspondences of {
   Prelude.Just correspondence ->
    decideOperationTraversal eqEntry eqOutcome residueEqual operationAccepts
      implementationEntries (snd operation) correspondence;
   Prelude.Nothing -> Prelude.False}

decideProviderQualification :: (a1 -> a1 -> Prelude.Bool) -> (a2 -> a2 ->
                               Prelude.Bool) -> (a3 -> a3 -> Prelude.Bool) ->
                               (a6 -> a6 -> Prelude.Bool) -> (a4 -> a5 ->
                               Prelude.Bool) -> Prelude.Bool -> Prelude.Bool
                               -> ([]
                               ((,) a1
                               (ContractOperationProjection a4 a3 a6))) ->
                               ([] ((,) a1 (CorrespondenceProjection a2 a3)))
                               -> ([]
                               ((,) a2
                               (ImplementationOperationProjection a5 a3 a6)))
                               -> Prelude.Bool
decideProviderQualification eqOperation eqEntry eqOutcome residueEqual operationAccepts contractRevisionMatches implementationRevisionMatches contractOperations correspondences implementationEntries =
  andb contractRevisionMatches
    (andb implementationRevisionMatches
      (andb (sameKeyDomainb eqOperation contractOperations correspondences)
        (allFiniteb
          (decideOperationAt eqOperation eqEntry eqOutcome residueEqual
            operationAccepts correspondences implementationEntries)
          contractOperations)))

