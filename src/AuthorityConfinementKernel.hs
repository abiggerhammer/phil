module AuthorityConfinementKernel where

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

decideClosureAuthorityConfinement :: Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool
decideClosureAuthorityConfinement publicSubsetReachable exercisedSubsetReachable exercisedSubsetPublic =
  andb publicSubsetReachable
    (andb exercisedSubsetReachable exercisedSubsetPublic)

decideNegativeAuthorityClaim :: Prelude.Bool -> Prelude.Bool
decideNegativeAuthorityClaim =
  negb

data ProviderAuthoritySubjectKind =
   SemanticProviderAuthoritySubjectKind
 | OpaqueForeignProviderAuthoritySubjectKind

decideProviderAuthoritySubject :: ProviderAuthoritySubjectKind ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool
decideProviderAuthoritySubject kind interfaceMatches definitionMatches =
  case kind of {
   SemanticProviderAuthoritySubjectKind ->
    andb interfaceMatches definitionMatches;
   OpaqueForeignProviderAuthoritySubjectKind -> Prelude.True}

data ProviderAuthorityInventoryBasisKind =
   CheckedPurePhilAuthorityInventoryKind
 | ForeignAuthorityInventoryByEvidenceKind
 | ForeignAuthorityInventoryAssumptionKind
 | ForeignAuthorityInventoryTcbBoundaryKind
 | ForeignAuthorityInventoryFromAbiShapeKind

decideProviderAuthorityInventoryBasis :: ProviderAuthoritySubjectKind ->
                                         ProviderAuthorityInventoryBasisKind
                                         -> Prelude.Bool
decideProviderAuthorityInventoryBasis subjectKind basisKind =
  case subjectKind of {
   SemanticProviderAuthoritySubjectKind ->
    case basisKind of {
     CheckedPurePhilAuthorityInventoryKind -> Prelude.True;
     _ -> Prelude.False};
   OpaqueForeignProviderAuthoritySubjectKind ->
    case basisKind of {
     CheckedPurePhilAuthorityInventoryKind -> Prelude.False;
     ForeignAuthorityInventoryFromAbiShapeKind -> Prelude.False;
     _ -> Prelude.True}}

decideProviderExtraAuthority :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
decideProviderExtraAuthority internal clientVisible =
  andb internal (negb clientVisible)

decideProviderStaticSummaries :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                 -> Prelude.Bool
decideProviderStaticSummaries staticReachableSubsetInternal staticPublicSubsetClientVisible staticExercisedSubsetClientVisible =
  andb staticReachableSubsetInternal
    (andb staticPublicSubsetClientVisible staticExercisedSubsetClientVisible)

data ProviderExtraAuthorityDispositionKind =
   ExtraAuthorityStaticallyConfinedKind
 | ExtraAuthorityExternallyConfinedKind
 | ExtraAuthorityAssumptionDependentKind
 | ExtraAuthorityTcbBoundaryKind
 | ExtraAuthorityAssertedAbsentFromAbiKind

decideProviderExtraDisposition :: ProviderAuthoritySubjectKind ->
                                  ProviderExtraAuthorityDispositionKind ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> Prelude.Bool
decideProviderExtraDisposition subjectKind dispositionKind staticReachable staticPublic staticExercised =
  case dispositionKind of {
   ExtraAuthorityStaticallyConfinedKind ->
    case subjectKind of {
     SemanticProviderAuthoritySubjectKind ->
      andb staticReachable (andb (negb staticPublic) (negb staticExercised));
     OpaqueForeignProviderAuthoritySubjectKind -> Prelude.False};
   ExtraAuthorityAssertedAbsentFromAbiKind -> Prelude.False;
   _ -> Prelude.True}

decideProviderAuthorityQualificationFacts :: Prelude.Bool -> Prelude.Bool ->
                                             Prelude.Bool -> Prelude.Bool ->
                                             Prelude.Bool -> Prelude.Bool
decideProviderAuthorityQualificationFacts subjectAccepted inventoryBasisAccepted staticSummariesAccepted dispositionDomainExactAccepted dispositionValuesAllowedAccepted =
  andb subjectAccepted
    (andb inventoryBasisAccepted
      (andb staticSummariesAccepted
        (andb dispositionDomainExactAccepted
          dispositionValuesAllowedAccepted)))

