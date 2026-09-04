module Phil.Systems.StorageCostAttributionCertification
  ( StorageCostLineageKernelFacts (..)
  , StorageRuntimeCostBinding (..)
  , StorageRuntimeCostBindingKernelFacts (..)
  , StorageCostAttributionCertificationError (..)
  , storageCostLineageKernelFacts
  , verifyStorageCostLineageKernelFacts
  , checkStorageCostLineageCertified
  , storageRuntimeCostBindingKernelFacts
  , verifyStorageRuntimeCostBindingKernelFacts
  , checkStorageRuntimeCostBindingCertified
  , certifyStorageCostAttribution
  ) where

import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Phil.Systems.CostAttribution
  ( CostAttributionStageBundle (..)
  , CostChargeIdentity
  , CostContribution (..)
  , CostContributionIdentity
  )
import Phil.Systems.IR
  ( CostClass
  , CostShape
  , costAllocationCount
  , costBytesCopied
  , costPeakLiveMemory
  )
import Phil.Systems.NextStageRequirement
  ( NextStageRequirementStageBundle (..)
  )
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , StageClosureVerificationError
  , verifyStageClosureBundle
  )
import Phil.Systems.Storage
import Phil.Systems.StorageRealizationCertification
  ( StorageRealizationCertificationError
  , checkStorageRealizationCertified
  )
import qualified StorageCostAttributionKernel as Kernel

-- | Exact native facts corresponding to StorageCostLineageValid plus the five
-- representation-neutral alternatives that witness AttributableStorageCost.
data StorageCostLineageKernelFacts = StorageCostLineageKernelFacts
  { storageCostKernelSubjectExact :: Bool
  , storageCostKernelPhysicalDomainExact :: Bool
  , storageCostKernelAllocationCountPresent :: Bool
  , storageCostKernelPeakLiveMemoryPresent :: Bool
  , storageCostKernelBytesCopiedPresent :: Bool
  , storageCostKernelResidencyRefPresent :: Bool
  , storageCostKernelCleanupRefPresent :: Bool
  }
  deriving (Eq, Show)

-- | Concrete witness for the proof-facing StorageRuntimeCostBinding. The
-- existing SYS-018 stage owns both identities and their functional relation.
data StorageRuntimeCostBinding = StorageRuntimeCostBinding
  { storageRuntimeCostContribution :: CostContributionIdentity
  , storageRuntimeCostCharge :: CostChargeIdentity
  }
  deriving (Eq, Show)

data StorageRuntimeCostBindingKernelFacts = StorageRuntimeCostBindingKernelFacts
  { storageRuntimeCostContributionInCharge :: Bool
  , storageRuntimeCostClassExact :: Bool
  , storageRuntimeCostShapeExact :: Bool
  }
  deriving (Eq, Show)

data StorageCostAttributionCertificationError
  = StorageCostAttributionRealizationError StorageRealizationCertificationError
  | StorageCostAttributionNativeStorageError StorageRealizationError
  | StorageCostAttributionLineageKernelDisagreement StorageCostLineageKernelFacts
  | StorageCostAttributionStageError StageClosureVerificationError
  | StorageCostAttributionUnknownContribution CostContributionIdentity
  | StorageCostAttributionMissingCharge CostContributionIdentity
  | StorageCostAttributionChargeMismatch CostChargeIdentity CostChargeIdentity
  | StorageCostAttributionClassMismatch CostClass CostClass
  | StorageCostAttributionShapeMismatch CostShape CostShape
  | StorageCostAttributionBindingKernelDisagreement StorageRuntimeCostBindingKernelFacts
  | StorageCostAttributionCertifiedKernelDisagreement
  deriving (Eq, Show)

-- | Preserve native MEM-006 diagnostics first, then require every exact
-- extracted storage-lineage classifier on the same concrete facts.
checkStorageCostLineageCertified
  :: CheckedStorageRealization
  -> StorageCostLineage
  -> Either StorageCostAttributionCertificationError CheckedStorageCostLineage
checkStorageCostLineageCertified checked lineage = do
  checkedLineage <- mapLeft StorageCostAttributionNativeStorageError $
    checkStorageCostLineage checked lineage
  verifyStorageCostLineageKernelFacts
    (storageCostLineageKernelFacts checked lineage)
  pure checkedLineage

storageCostLineageKernelFacts
  :: CheckedStorageRealization
  -> StorageCostLineage
  -> StorageCostLineageKernelFacts
storageCostLineageKernelFacts checked lineage =
  StorageCostLineageKernelFacts
    { storageCostKernelSubjectExact =
        storageIdentitySubject (checkedStorageSemanticIdentity checked)
          == storageCostSubject lineage
    , storageCostKernelPhysicalDomainExact =
        checkedStoragePhysicalObjects checked == storageCostPhysicalObjects lineage
    , storageCostKernelAllocationCountPresent =
        isJust (costAllocationCount shape)
    , storageCostKernelPeakLiveMemoryPresent =
        isJust (costPeakLiveMemory shape)
    , storageCostKernelBytesCopiedPresent =
        isJust (costBytesCopied shape)
    , storageCostKernelResidencyRefPresent =
        not (Set.null (storageCostResidencyRefs lineage))
    , storageCostKernelCleanupRefPresent =
        not (Set.null (storageCostCleanupRefs lineage))
    }
  where
    shape = storageCostShape lineage

verifyStorageCostLineageKernelFacts
  :: StorageCostLineageKernelFacts
  -> Either StorageCostAttributionCertificationError ()
verifyStorageCostLineageKernelFacts facts =
  let subjectExact = storageCostKernelSubjectExact facts
      physicalDomainExact = storageCostKernelPhysicalDomainExact facts
      attributable = Kernel.decideAttributableStorageCostByFacts
        (storageCostKernelAllocationCountPresent facts)
        (storageCostKernelPeakLiveMemoryPresent facts)
        (storageCostKernelBytesCopiedPresent facts)
        (storageCostKernelResidencyRefPresent facts)
        (storageCostKernelCleanupRefPresent facts)
      accepted =
        Kernel.decideStorageCostSubjectExactByFacts subjectExact
          && Kernel.decideStorageCostPhysicalDomainExactByFacts physicalDomainExact
          && attributable
          && Kernel.decideStorageCostLineageValidByFacts
            subjectExact physicalDomainExact attributable
  in if accepted
      then Right ()
      else Left (StorageCostAttributionLineageKernelDisagreement facts)

-- | Reflect the exact SYS-018 contribution->charge map and the exact selected
-- CostClass/CostShape into the StorageRuntimeCostBinding machine gate.
storageRuntimeCostBindingKernelFacts
  :: StageClosureBundle
  -> StorageCostLineage
  -> StorageRuntimeCostBinding
  -> Either StorageCostAttributionCertificationError StorageRuntimeCostBindingKernelFacts
storageRuntimeCostBindingKernelFacts stage lineage binding = do
  let costStage = nextStageRequirementStageBase (stageClosureNextStage stage)
      contributionId = storageRuntimeCostContribution binding
      requestedCharge = storageRuntimeCostCharge binding
  contribution <- maybe
    (Left (StorageCostAttributionUnknownContribution contributionId))
    Right
    (Map.lookup contributionId (costAttributionStageContributions costStage))
  actualCharge <- maybe
    (Left (StorageCostAttributionMissingCharge contributionId))
    Right
    (Map.lookup contributionId (costAttributionStageContributionCharges costStage))
  if requestedCharge == actualCharge
    then Right ()
    else Left (StorageCostAttributionChargeMismatch actualCharge requestedCharge)
  if costContributionClass contribution == storageCostClass lineage
    then Right ()
    else Left (StorageCostAttributionClassMismatch
      (costContributionClass contribution) (storageCostClass lineage))
  if costContributionShape contribution == storageCostShape lineage
    then Right ()
    else Left (StorageCostAttributionShapeMismatch
      (costContributionShape contribution) (storageCostShape lineage))
  pure StorageRuntimeCostBindingKernelFacts
    { storageRuntimeCostContributionInCharge = True
    , storageRuntimeCostClassExact = True
    , storageRuntimeCostShapeExact = True
    }

verifyStorageRuntimeCostBindingKernelFacts
  :: StorageRuntimeCostBindingKernelFacts
  -> Either StorageCostAttributionCertificationError ()
verifyStorageRuntimeCostBindingKernelFacts facts =
  if Kernel.decideStorageRuntimeCostBindingByFacts
      (storageRuntimeCostContributionInCharge facts)
      (storageRuntimeCostClassExact facts)
      (storageRuntimeCostShapeExact facts)
    then Right ()
    else Left (StorageCostAttributionBindingKernelDisagreement facts)

-- | StageClosure is the existing production integration point for the complete
-- native SYS-015/016/018 chain and the exact SystemsRuntimeGraph kernel.
checkStorageRuntimeCostBindingCertified
  :: StageClosureBundle
  -> StorageCostLineage
  -> StorageRuntimeCostBinding
  -> Either StorageCostAttributionCertificationError ()
checkStorageRuntimeCostBindingCertified stage lineage binding = do
  mapLeft StorageCostAttributionStageError $ verifyStageClosureBundle stage
  facts <- storageRuntimeCostBindingKernelFacts stage lineage binding
  verifyStorageRuntimeCostBindingKernelFacts facts

-- | Compose implementation-refined MEM-001, native-first MEM-006 lineage
-- checking, the production-bound runtime graph, the exact storage/runtime
-- binding, and the outer CertifiedStorageCostAttribution machine gate.
certifyStorageCostAttribution
  :: StageClosureBundle
  -> StorageRealizationRelation
  -> StorageCostLineage
  -> StorageRuntimeCostBinding
  -> Either StorageCostAttributionCertificationError CheckedStorageCostLineage
certifyStorageCostAttribution stage relation lineage binding = do
  checked <- mapLeft StorageCostAttributionRealizationError $
    checkStorageRealizationCertified relation
  checkedLineage <- checkStorageCostLineageCertified checked lineage
  checkStorageRuntimeCostBindingCertified stage lineage binding
  if Kernel.decideCertifiedStorageCostAttributionByFacts True True True
    then Right checkedLineage
    else Left StorageCostAttributionCertifiedKernelDisagreement

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
