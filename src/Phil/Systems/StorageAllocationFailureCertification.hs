module Phil.Systems.StorageAllocationFailureCertification
  ( StorageAllocationFailureDispositionKernelFacts (..)
  , StorageAllocationFailureCertificationError (..)
  , storageAllocationFailureDispositionKernelFacts
  , verifyStorageAllocationFailureDispositionKernelFacts
  , verifyStorageAllocationFailureRealizationKernelFacts
  , checkStorageAllocationFailureCertified
  ) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Systems.Storage
import Phil.Systems.StorageRealizationCertification
import qualified StorageAllocationFailureKernel as Kernel

-- | Native reflections of the exact Certified StorageFailureDispositionValid
-- case split from PHIL-MEM-FAIL-001. The implementation-refined MEM-001 base
-- realization is deliberately represented separately as one predecessor fact.
data StorageAllocationFailureDispositionKernelFacts
  = StorageFailureCannotFailKernelFacts
  | StorageFailureMapsToSourceKernelFacts
      { storageFailureKernelMappedIdentityValid :: Bool
      , storageFailureKernelMappedDeclared :: Bool
      }
  | StorageFailureProvedUnreachableKernelFacts
      { storageFailureKernelEvidenceIdentityValid :: Bool
      }
  | StorageFailureAssumptionKernelFacts
      { storageFailureKernelAssumptionIdentityValid :: Bool
      }
  | StorageFailureDeploymentRequirementKernelFacts
      { storageFailureKernelRequirementIdentityValid :: Bool
      }
  | StorageFailureUnaccountedKernelFacts
  deriving (Eq, Show)

data StorageAllocationFailureCertificationError
  = StorageAllocationFailureCertificationPredecessorError
      StorageRealizationCertificationError
  | StorageAllocationFailureCertificationDispositionKernelDisagreement
      StorageAllocationFailureDispositionKernelFacts
  | StorageAllocationFailureCertificationRealizationKernelDisagreement
      Bool Bool
  deriving (Eq, Show)

-- | Preserve all existing Storage diagnostics and the implementation-refined
-- MEM-001 predecessor gate, then independently require the exact extracted
-- MEM-002/MEM-003 disposition classifier and outer composition gate.
checkStorageAllocationFailureCertified
  :: StorageRealizationRelation
  -> Either StorageAllocationFailureCertificationError CheckedStorageRealization
checkStorageAllocationFailureCertified relation = do
  checked <- mapLeft StorageAllocationFailureCertificationPredecessorError $
    checkStorageRealizationCertified relation
  let facts = storageAllocationFailureDispositionKernelFacts relation
  dispositionAccepted <- verifyStorageAllocationFailureDispositionKernelFacts facts
  verifyStorageAllocationFailureRealizationKernelFacts True dispositionAccepted
  pure checked

storageAllocationFailureDispositionKernelFacts
  :: StorageRealizationRelation
  -> StorageAllocationFailureDispositionKernelFacts
storageAllocationFailureDispositionKernelFacts relation =
  case storageRelationAllocationFailure relation of
    PhysicalAllocationCannotFail -> StorageFailureCannotFailKernelFacts
    PhysicalAllocationMayFail disposition -> case disposition of
      StorageFailureMapsToSource failure ->
        StorageFailureMapsToSourceKernelFacts
          { storageFailureKernelMappedIdentityValid =
              not (Text.null (unStorageFailureKey failure))
          , storageFailureKernelMappedDeclared =
              sourceFailureContainsNative
                failure
                (storageRelationSourceFailureSurface relation)
          }
      StorageFailureProvedUnreachable evidence ->
        StorageFailureProvedUnreachableKernelFacts
          { storageFailureKernelEvidenceIdentityValid =
              not (Text.null (unStorageCapacityEvidenceKey evidence))
          }
      StorageFailureAssumption assumption ->
        StorageFailureAssumptionKernelFacts
          { storageFailureKernelAssumptionIdentityValid =
              not (Text.null (unStorageAssumptionKey assumption))
          }
      StorageFailureDeploymentRequirement requirement ->
        StorageFailureDeploymentRequirementKernelFacts
          { storageFailureKernelRequirementIdentityValid =
              not (Text.null (unStorageDeploymentRequirementKey requirement))
          }
      StorageFailureUnaccounted -> StorageFailureUnaccountedKernelFacts

verifyStorageAllocationFailureDispositionKernelFacts
  :: StorageAllocationFailureDispositionKernelFacts
  -> Either StorageAllocationFailureCertificationError Bool
verifyStorageAllocationFailureDispositionKernelFacts facts =
  if accepted
    then Right True
    else Left
      (StorageAllocationFailureCertificationDispositionKernelDisagreement facts)
  where
    accepted = case facts of
      StorageFailureCannotFailKernelFacts ->
        Kernel.decideStorageFailureCannotFailByFacts
      StorageFailureMapsToSourceKernelFacts identityValid declared ->
        Kernel.decideStorageFailureMapsToSourceByFacts identityValid declared
      StorageFailureProvedUnreachableKernelFacts identityValid ->
        Kernel.decideStorageFailureProvedUnreachableByFacts identityValid
      StorageFailureAssumptionKernelFacts identityValid ->
        Kernel.decideStorageFailureAssumptionByFacts identityValid
      StorageFailureDeploymentRequirementKernelFacts identityValid ->
        Kernel.decideStorageFailureDeploymentRequirementByFacts identityValid
      StorageFailureUnaccountedKernelFacts ->
        Kernel.decideStorageFailureUnaccountedByFacts

verifyStorageAllocationFailureRealizationKernelFacts
  :: Bool
  -> Bool
  -> Either StorageAllocationFailureCertificationError ()
verifyStorageAllocationFailureRealizationKernelFacts
    baseRealizationValid dispositionValid =
  if Kernel.decideStorageFailureRealizationByFacts
      baseRealizationValid dispositionValid
    then Right ()
    else Left
      (StorageAllocationFailureCertificationRealizationKernelDisagreement
        baseRealizationValid dispositionValid)

sourceFailureContainsNative
  :: StorageFailureKey
  -> SourceStorageFailureSurface
  -> Bool
sourceFailureContainsNative _ SourceStorageInfallible = False
sourceFailureContainsNative failure (SourceStorageFailures failures) =
  Set.member failure failures

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
