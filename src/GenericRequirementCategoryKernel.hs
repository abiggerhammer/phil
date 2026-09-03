module GenericRequirementCategoryKernel where

import qualified Prelude

data GenericRequirementCategory =
   GenericStructuralCategory
 | GenericPropositionCategory
 | GenericProviderCategory
 | GenericCallableCategory
 | GenericBoundaryCategory
 | GenericArchitectureCategory
 | GenericEffectsCategory
 | GenericAuthorityCategory
 | GenericBoundaryRepresentationCategory
 | GenericRepresentationCategory
 | GenericPlacementCategory
 | GenericCostCategory
 | GenericEnvironmentCategory

data GenericRequirementCompetence =
   StructuralRequirementChecker
 | PropositionRequirementChecker
 | ProviderRequirementChecker
 | CallableRequirementChecker
 | BoundaryRequirementChecker
 | ArchitectureRequirementChecker
 | EffectsRequirementChecker
 | AuthorityRequirementChecker
 | BoundaryRepresentationRequirementChecker
 | RepresentationRequirementChecker
 | PlacementRequirementChecker
 | CostRequirementChecker
 | EnvironmentRequirementChecker

competenceForRequirementCategory :: GenericRequirementCategory ->
                                    GenericRequirementCompetence
competenceForRequirementCategory category =
  case category of {
   GenericStructuralCategory -> StructuralRequirementChecker;
   GenericPropositionCategory -> PropositionRequirementChecker;
   GenericProviderCategory -> ProviderRequirementChecker;
   GenericCallableCategory -> CallableRequirementChecker;
   GenericBoundaryCategory -> BoundaryRequirementChecker;
   GenericArchitectureCategory -> ArchitectureRequirementChecker;
   GenericEffectsCategory -> EffectsRequirementChecker;
   GenericAuthorityCategory -> AuthorityRequirementChecker;
   GenericBoundaryRepresentationCategory ->
    BoundaryRepresentationRequirementChecker;
   GenericRepresentationCategory -> RepresentationRequirementChecker;
   GenericPlacementCategory -> PlacementRequirementChecker;
   GenericCostCategory -> CostRequirementChecker;
   GenericEnvironmentCategory -> EnvironmentRequirementChecker}

data RequirementHandoffDecision =
   RequirementHandoffKeyDecision
 | RequirementHandoffCategoryDecision
 | RequirementHandoffTargetDecision
 | RequirementCheckedKeyDecision
 | RequirementCheckedCategoryDecision
 | RequirementCheckedSemanticFormDecision
 | RequirementCheckedCompetenceDecision
 | RequirementHandoffAcceptedDecision

decideRequirementHandoffByFacts :: Prelude.Bool -> Prelude.Bool ->
                                   Prelude.Bool -> Prelude.Bool ->
                                   Prelude.Bool -> Prelude.Bool ->
                                   Prelude.Bool -> RequirementHandoffDecision
decideRequirementHandoffByFacts handoffKeyMatches handoffCategoryMatches handoffTargetMatches checkedKeyMatches checkedCategoryMatches checkedSemanticFormMatches checkedCompetenceMatches =
  case handoffKeyMatches of {
   Prelude.True ->
    case handoffCategoryMatches of {
     Prelude.True ->
      case handoffTargetMatches of {
       Prelude.True ->
        case checkedKeyMatches of {
         Prelude.True ->
          case checkedCategoryMatches of {
           Prelude.True ->
            case checkedSemanticFormMatches of {
             Prelude.True ->
              case checkedCompetenceMatches of {
               Prelude.True -> RequirementHandoffAcceptedDecision;
               Prelude.False -> RequirementCheckedCompetenceDecision};
             Prelude.False -> RequirementCheckedSemanticFormDecision};
           Prelude.False -> RequirementCheckedCategoryDecision};
         Prelude.False -> RequirementCheckedKeyDecision};
       Prelude.False -> RequirementHandoffTargetDecision};
     Prelude.False -> RequirementHandoffCategoryDecision};
   Prelude.False -> RequirementHandoffKeyDecision}

data RequirementInterfaceDomainDecision =
   RequirementInterfaceHandoffDomainDecision
 | RequirementInterfaceCheckedDomainDecision
 | RequirementInterfaceDomainAcceptedDecision

decideRequirementInterfaceDomainByFacts :: Prelude.Bool -> Prelude.Bool ->
                                           RequirementInterfaceDomainDecision
decideRequirementInterfaceDomainByFacts handoffDomainExact checkedDomainExact =
  case handoffDomainExact of {
   Prelude.True ->
    case checkedDomainExact of {
     Prelude.True -> RequirementInterfaceDomainAcceptedDecision;
     Prelude.False -> RequirementInterfaceCheckedDomainDecision};
   Prelude.False -> RequirementInterfaceHandoffDomainDecision}
