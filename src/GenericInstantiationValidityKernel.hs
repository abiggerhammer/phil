module GenericInstantiationValidityKernel where

import qualified Prelude

data GenericRequirementKind =
   GenericStructuralRequirementKind
 | GenericProviderRequirementKind
 | GenericPropositionRequirementKind

data GenericDispositionKind =
   GenericStructuralModeDispositionKind
 | GenericExactProviderDispositionKind
 | GenericProviderRefinementDispositionKind
 | GenericEvidenceDispositionKind
 | GenericAssumptionDispositionKind
 | GenericExportDispositionKind

data GenericDispositionValidityFacts =
   MkGenericDispositionValidityFacts GenericRequirementKind GenericDispositionKind 
 Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool

validityRequirementKind :: GenericDispositionValidityFacts ->
                           GenericRequirementKind
validityRequirementKind g =
  case g of {
   MkGenericDispositionValidityFacts validityRequirementKind0 _ _ _ _ _ _
    _ -> validityRequirementKind0}

validityDispositionKind :: GenericDispositionValidityFacts ->
                           GenericDispositionKind
validityDispositionKind g =
  case g of {
   MkGenericDispositionValidityFacts _ validityDispositionKind0 _ _ _ _ _
    _ -> validityDispositionKind0}

validityStructuralModeAllows :: GenericDispositionValidityFacts ->
                                Prelude.Bool
validityStructuralModeAllows g =
  case g of {
   MkGenericDispositionValidityFacts _ _ validityStructuralModeAllows0 _ _ _
    _ _ -> validityStructuralModeAllows0}

validityExactProviderMatches :: GenericDispositionValidityFacts ->
                                Prelude.Bool
validityExactProviderMatches g =
  case g of {
   MkGenericDispositionValidityFacts _ _ _ validityExactProviderMatches0 _ _
    _ _ -> validityExactProviderMatches0}

validityProviderRefinementTargets :: GenericDispositionValidityFacts ->
                                     Prelude.Bool
validityProviderRefinementTargets g =
  case g of {
   MkGenericDispositionValidityFacts _ _ _ _
    validityProviderRefinementTargets0 _ _ _ ->
    validityProviderRefinementTargets0}

validityPropositionEvidenceMatches :: GenericDispositionValidityFacts ->
                                      Prelude.Bool
validityPropositionEvidenceMatches g =
  case g of {
   MkGenericDispositionValidityFacts _ _ _ _ _
    validityPropositionEvidenceMatches0 _ _ ->
    validityPropositionEvidenceMatches0}

validityAllowsAssumptions :: GenericDispositionValidityFacts -> Prelude.Bool
validityAllowsAssumptions g =
  case g of {
   MkGenericDispositionValidityFacts _ _ _ _ _ _ validityAllowsAssumptions0
    _ -> validityAllowsAssumptions0}

validityAllowsExports :: GenericDispositionValidityFacts -> Prelude.Bool
validityAllowsExports g =
  case g of {
   MkGenericDispositionValidityFacts _ _ _ _ _ _ _ validityAllowsExports0 ->
    validityAllowsExports0}

data GenericDispositionValidityDecision =
   GenericDispositionValidityAccepted
 | GenericDispositionValidityStructuralRejected
 | GenericDispositionValidityProviderInterfaceMismatch
 | GenericDispositionValidityProviderRefinementMismatch
 | GenericDispositionValidityPropositionEvidenceMismatch
 | GenericDispositionValidityAssumptionNotPermitted
 | GenericDispositionValidityExportNotPermitted
 | GenericDispositionValidityKindMismatch

decideGenericDispositionValidity :: GenericDispositionValidityFacts ->
                                    GenericDispositionValidityDecision
decideGenericDispositionValidity facts =
  case validityDispositionKind facts of {
   GenericStructuralModeDispositionKind ->
    case validityRequirementKind facts of {
     GenericStructuralRequirementKind ->
      case validityStructuralModeAllows facts of {
       Prelude.True -> GenericDispositionValidityAccepted;
       Prelude.False -> GenericDispositionValidityStructuralRejected};
     _ -> GenericDispositionValidityKindMismatch};
   GenericExactProviderDispositionKind ->
    case validityRequirementKind facts of {
     GenericProviderRequirementKind ->
      case validityExactProviderMatches facts of {
       Prelude.True -> GenericDispositionValidityAccepted;
       Prelude.False -> GenericDispositionValidityProviderInterfaceMismatch};
     _ -> GenericDispositionValidityKindMismatch};
   GenericProviderRefinementDispositionKind ->
    case validityRequirementKind facts of {
     GenericProviderRequirementKind ->
      case validityProviderRefinementTargets facts of {
       Prelude.True -> GenericDispositionValidityAccepted;
       Prelude.False -> GenericDispositionValidityProviderRefinementMismatch};
     _ -> GenericDispositionValidityKindMismatch};
   GenericEvidenceDispositionKind ->
    case validityRequirementKind facts of {
     GenericPropositionRequirementKind ->
      case validityPropositionEvidenceMatches facts of {
       Prelude.True -> GenericDispositionValidityAccepted;
       Prelude.False -> GenericDispositionValidityPropositionEvidenceMismatch};
     _ -> GenericDispositionValidityKindMismatch};
   GenericAssumptionDispositionKind ->
    case validityAllowsAssumptions facts of {
     Prelude.True -> GenericDispositionValidityAccepted;
     Prelude.False -> GenericDispositionValidityAssumptionNotPermitted};
   GenericExportDispositionKind ->
    case validityAllowsExports facts of {
     Prelude.True -> GenericDispositionValidityAccepted;
     Prelude.False -> GenericDispositionValidityExportNotPermitted}}
