module GenericIdentityEqualityKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

data GenericApplicationEqualityFacts =
   MkGenericApplicationEqualityFacts Prelude.Bool Prelude.Bool Prelude.Bool

applicationDeclarationMatches :: GenericApplicationEqualityFacts ->
                                 Prelude.Bool
applicationDeclarationMatches g =
  case g of {
   MkGenericApplicationEqualityFacts applicationDeclarationMatches0 _ _ ->
    applicationDeclarationMatches0}

applicationInterfaceMatches :: GenericApplicationEqualityFacts ->
                               Prelude.Bool
applicationInterfaceMatches g =
  case g of {
   MkGenericApplicationEqualityFacts _ applicationInterfaceMatches0 _ ->
    applicationInterfaceMatches0}

applicationArgumentsMatch :: GenericApplicationEqualityFacts -> Prelude.Bool
applicationArgumentsMatch g =
  case g of {
   MkGenericApplicationEqualityFacts _ _ applicationArgumentsMatch0 ->
    applicationArgumentsMatch0}

sameApplicationFactsb :: GenericApplicationEqualityFacts -> Prelude.Bool
sameApplicationFactsb facts =
  andb (applicationDeclarationMatches facts)
    (andb (applicationInterfaceMatches facts)
      (applicationArgumentsMatch facts))

data GenericApplicationEqualityDecision =
   GenericApplicationEqual
 | GenericApplicationDifferent

decideGenericApplicationEquality :: GenericApplicationEqualityFacts ->
                                    GenericApplicationEqualityDecision
decideGenericApplicationEquality facts =
  case sameApplicationFactsb facts of {
   Prelude.True -> GenericApplicationEqual;
   Prelude.False -> GenericApplicationDifferent}

data GenericDischargeLineageEqualityFacts =
   MkGenericDischargeLineageEqualityFacts Prelude.Bool Prelude.Bool Prelude.Bool

lineageApplicationMatches :: GenericDischargeLineageEqualityFacts ->
                             Prelude.Bool
lineageApplicationMatches g =
  case g of {
   MkGenericDischargeLineageEqualityFacts lineageApplicationMatches0 _ _ ->
    lineageApplicationMatches0}

lineageDefinitionMatches :: GenericDischargeLineageEqualityFacts ->
                            Prelude.Bool
lineageDefinitionMatches g =
  case g of {
   MkGenericDischargeLineageEqualityFacts _ lineageDefinitionMatches0 _ ->
    lineageDefinitionMatches0}

lineageEvidenceMatches :: GenericDischargeLineageEqualityFacts ->
                          Prelude.Bool
lineageEvidenceMatches g =
  case g of {
   MkGenericDischargeLineageEqualityFacts _ _ lineageEvidenceMatches0 ->
    lineageEvidenceMatches0}

sameDischargeLineageFactsb :: GenericDischargeLineageEqualityFacts ->
                              Prelude.Bool
sameDischargeLineageFactsb facts =
  andb (lineageApplicationMatches facts)
    (andb (lineageDefinitionMatches facts) (lineageEvidenceMatches facts))

data GenericDischargeLineageEqualityDecision =
   GenericDischargeLineageEqual
 | GenericDischargeLineageDifferent

decideGenericDischargeLineageEquality :: GenericDischargeLineageEqualityFacts
                                         ->
                                         GenericDischargeLineageEqualityDecision
decideGenericDischargeLineageEquality facts =
  case sameDischargeLineageFactsb facts of {
   Prelude.True -> GenericDischargeLineageEqual;
   Prelude.False -> GenericDischargeLineageDifferent}

