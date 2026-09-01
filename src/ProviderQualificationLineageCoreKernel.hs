module ProviderQualificationLineageCoreKernel where

import qualified Prelude

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> b2}

existsb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
existsb f l =
  case l of {
   [] -> Prelude.False;
   (:) a l0 -> orb (f a) (existsb f l0)}

data QualificationIdentityDecision =
   QualificationIdentityAcceptedDecision
 | QualificationEvidenceClaimDecision
 | QualificationAdmissionClaimDecision
 | QualificationAdmissionEvidenceDecision
 | QualificationAdmissionInterfaceDecision

decideQualificationIdentityByFacts :: Prelude.Bool -> Prelude.Bool ->
                                      Prelude.Bool -> Prelude.Bool ->
                                      QualificationIdentityDecision
decideQualificationIdentityByFacts evidenceClaimExact admissionClaimExact admissionEvidenceExact admissionInterfaceExact =
  case evidenceClaimExact of {
   Prelude.True ->
    case admissionClaimExact of {
     Prelude.True ->
      case admissionEvidenceExact of {
       Prelude.True ->
        case admissionInterfaceExact of {
         Prelude.True -> QualificationIdentityAcceptedDecision;
         Prelude.False -> QualificationAdmissionInterfaceDecision};
       Prelude.False -> QualificationAdmissionEvidenceDecision};
     Prelude.False -> QualificationAdmissionClaimDecision};
   Prelude.False -> QualificationEvidenceClaimDecision}

data QualificationRegistryDecision =
   QualificationRegistryAcceptedDecision
 | QualificationNodeKeyDecision
 | QualificationGroundKeyDecision

decideQualificationRegistryByFacts :: Prelude.Bool -> Prelude.Bool ->
                                      QualificationRegistryDecision
decideQualificationRegistryByFacts nodeKeysExact groundKeysExact =
  case nodeKeysExact of {
   Prelude.True ->
    case groundKeysExact of {
     Prelude.True -> QualificationRegistryAcceptedDecision;
     Prelude.False -> QualificationGroundKeyDecision};
   Prelude.False -> QualificationNodeKeyDecision}

data QualificationRootDecision =
   QualificationRootAcceptedDecision
 | QualificationUnknownRootDecision

decideQualificationRootByFacts :: Prelude.Bool -> QualificationRootDecision
decideQualificationRootByFacts rootKnown =
  case rootKnown of {
   Prelude.True -> QualificationRootAcceptedDecision;
   Prelude.False -> QualificationUnknownRootDecision}

data QualificationDependencyNodeDecision =
   QualificationDependencyNodeAcceptedDecision
 | QualificationRejectedAdmissionDecision
 | QualificationUnknownAdmissionDecision
 | QualificationUnknownGroundDecision
 | QualificationRejectedGroundDecision

decideQualificationDependencyNodeByFacts :: Prelude.Bool -> Prelude.Bool ->
                                            Prelude.Bool -> Prelude.Bool ->
                                            QualificationDependencyNodeDecision
decideQualificationDependencyNodeByFacts admissionAccepted admissionDependenciesKnown groundsKnown groundsAccepted =
  case admissionAccepted of {
   Prelude.True ->
    case admissionDependenciesKnown of {
     Prelude.True ->
      case groundsKnown of {
       Prelude.True ->
        case groundsAccepted of {
         Prelude.True -> QualificationDependencyNodeAcceptedDecision;
         Prelude.False -> QualificationRejectedGroundDecision};
       Prelude.False -> QualificationUnknownGroundDecision};
     Prelude.False -> QualificationUnknownAdmissionDecision};
   Prelude.False -> QualificationRejectedAdmissionDecision}

propagateGroundPresence :: Prelude.Bool -> ([] Prelude.Bool) -> Prelude.Bool
propagateGroundPresence ownGroundPresent dependencyGroundPresence =
  orb ownGroundPresent (existsb (\value -> value) dependencyGroundPresence)

data QualificationDependencyClosureDecision =
   QualificationDependencyClosureAcceptedDecision
 | QualificationDependencyUngroundedDecision

decideQualificationDependencyClosureByFacts :: Prelude.Bool ->
                                               QualificationDependencyClosureDecision
decideQualificationDependencyClosureByFacts allReachableGrounded =
  case allReachableGrounded of {
   Prelude.True -> QualificationDependencyClosureAcceptedDecision;
   Prelude.False -> QualificationDependencyUngroundedDecision}
