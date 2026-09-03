module Phil.Core.GenericRequirementCategoryKernelBridge
  ( KernelRequirementCategory (..)
  , KernelRequirementCompetence (..)
  , RequirementHandoffClassification (..)
  , RequirementInterfaceDomainClassification (..)
  , certifiedCompetenceForKernelCategory
  , classifyRequirementHandoffFacts
  , classifyRequirementInterfaceDomainFacts
  ) where

import qualified GenericRequirementCategoryKernel as Kernel

data KernelRequirementCategory
  = KernelStructuralCategory
  | KernelPropositionCategory
  | KernelProviderCategory
  | KernelCallableCategory
  | KernelBoundaryCategory
  | KernelArchitectureCategory
  | KernelEffectsCategory
  | KernelAuthorityCategory
  | KernelBoundaryRepresentationCategory
  | KernelRepresentationCategory
  | KernelPlacementCategory
  | KernelCostCategory
  | KernelEnvironmentCategory
  deriving (Eq, Show)

data KernelRequirementCompetence
  = KernelStructuralRequirementChecker
  | KernelPropositionRequirementChecker
  | KernelProviderRequirementChecker
  | KernelCallableRequirementChecker
  | KernelBoundaryRequirementChecker
  | KernelArchitectureRequirementChecker
  | KernelEffectsRequirementChecker
  | KernelAuthorityRequirementChecker
  | KernelBoundaryRepresentationRequirementChecker
  | KernelRepresentationRequirementChecker
  | KernelPlacementRequirementChecker
  | KernelCostRequirementChecker
  | KernelEnvironmentRequirementChecker
  deriving (Eq, Show)

data RequirementHandoffClassification
  = RequirementHandoffKeyClassification
  | RequirementHandoffCategoryClassification
  | RequirementHandoffTargetClassification
  | RequirementCheckedKeyClassification
  | RequirementCheckedCategoryClassification
  | RequirementCheckedSemanticFormClassification
  | RequirementCheckedCompetenceClassification
  | RequirementHandoffAcceptedClassification
  deriving (Eq, Show)

data RequirementInterfaceDomainClassification
  = RequirementInterfaceHandoffDomainClassification
  | RequirementInterfaceCheckedDomainClassification
  | RequirementInterfaceDomainAcceptedClassification
  deriving (Eq, Show)

certifiedCompetenceForKernelCategory
  :: KernelRequirementCategory
  -> KernelRequirementCompetence
certifiedCompetenceForKernelCategory =
  fromExtractedCompetence . Kernel.competenceForRequirementCategory . toExtractedCategory

classifyRequirementHandoffFacts
  :: Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> RequirementHandoffClassification
classifyRequirementHandoffFacts handoffKeyMatches handoffCategoryMatches
    handoffTargetMatches checkedKeyMatches checkedCategoryMatches
    checkedSemanticFormMatches checkedCompetenceMatches =
  case Kernel.decideRequirementHandoffByFacts
      handoffKeyMatches
      handoffCategoryMatches
      handoffTargetMatches
      checkedKeyMatches
      checkedCategoryMatches
      checkedSemanticFormMatches
      checkedCompetenceMatches of
    Kernel.RequirementHandoffKeyDecision -> RequirementHandoffKeyClassification
    Kernel.RequirementHandoffCategoryDecision -> RequirementHandoffCategoryClassification
    Kernel.RequirementHandoffTargetDecision -> RequirementHandoffTargetClassification
    Kernel.RequirementCheckedKeyDecision -> RequirementCheckedKeyClassification
    Kernel.RequirementCheckedCategoryDecision -> RequirementCheckedCategoryClassification
    Kernel.RequirementCheckedSemanticFormDecision ->
      RequirementCheckedSemanticFormClassification
    Kernel.RequirementCheckedCompetenceDecision ->
      RequirementCheckedCompetenceClassification
    Kernel.RequirementHandoffAcceptedDecision -> RequirementHandoffAcceptedClassification

classifyRequirementInterfaceDomainFacts
  :: Bool
  -> Bool
  -> RequirementInterfaceDomainClassification
classifyRequirementInterfaceDomainFacts handoffDomainExact checkedDomainExact =
  case Kernel.decideRequirementInterfaceDomainByFacts
      handoffDomainExact checkedDomainExact of
    Kernel.RequirementInterfaceHandoffDomainDecision ->
      RequirementInterfaceHandoffDomainClassification
    Kernel.RequirementInterfaceCheckedDomainDecision ->
      RequirementInterfaceCheckedDomainClassification
    Kernel.RequirementInterfaceDomainAcceptedDecision ->
      RequirementInterfaceDomainAcceptedClassification

toExtractedCategory
  :: KernelRequirementCategory
  -> Kernel.GenericRequirementCategory
toExtractedCategory category = case category of
  KernelStructuralCategory -> Kernel.GenericStructuralCategory
  KernelPropositionCategory -> Kernel.GenericPropositionCategory
  KernelProviderCategory -> Kernel.GenericProviderCategory
  KernelCallableCategory -> Kernel.GenericCallableCategory
  KernelBoundaryCategory -> Kernel.GenericBoundaryCategory
  KernelArchitectureCategory -> Kernel.GenericArchitectureCategory
  KernelEffectsCategory -> Kernel.GenericEffectsCategory
  KernelAuthorityCategory -> Kernel.GenericAuthorityCategory
  KernelBoundaryRepresentationCategory -> Kernel.GenericBoundaryRepresentationCategory
  KernelRepresentationCategory -> Kernel.GenericRepresentationCategory
  KernelPlacementCategory -> Kernel.GenericPlacementCategory
  KernelCostCategory -> Kernel.GenericCostCategory
  KernelEnvironmentCategory -> Kernel.GenericEnvironmentCategory

fromExtractedCompetence
  :: Kernel.GenericRequirementCompetence
  -> KernelRequirementCompetence
fromExtractedCompetence competence = case competence of
  Kernel.StructuralRequirementChecker -> KernelStructuralRequirementChecker
  Kernel.PropositionRequirementChecker -> KernelPropositionRequirementChecker
  Kernel.ProviderRequirementChecker -> KernelProviderRequirementChecker
  Kernel.CallableRequirementChecker -> KernelCallableRequirementChecker
  Kernel.BoundaryRequirementChecker -> KernelBoundaryRequirementChecker
  Kernel.ArchitectureRequirementChecker -> KernelArchitectureRequirementChecker
  Kernel.EffectsRequirementChecker -> KernelEffectsRequirementChecker
  Kernel.AuthorityRequirementChecker -> KernelAuthorityRequirementChecker
  Kernel.BoundaryRepresentationRequirementChecker ->
    KernelBoundaryRepresentationRequirementChecker
  Kernel.RepresentationRequirementChecker -> KernelRepresentationRequirementChecker
  Kernel.PlacementRequirementChecker -> KernelPlacementRequirementChecker
  Kernel.CostRequirementChecker -> KernelCostRequirementChecker
  Kernel.EnvironmentRequirementChecker -> KernelEnvironmentRequirementChecker
