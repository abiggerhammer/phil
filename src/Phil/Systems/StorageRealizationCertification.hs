module Phil.Systems.StorageRealizationCertification
  ( StorageRealizationKernelFacts (..)
  , StorageRealizationCertificationError (..)
  , storageRealizationKernelFacts
  , verifyStorageRealizationKernelFacts
  , checkStorageRealizationCertified
  ) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Static (RealizationRevision (..))
import Phil.Systems.Storage
import qualified StorageRealizationKernel as Kernel

-- | Native reflections of the seven representation-neutral facts proved
-- equivalent to StorageRealizationValid by PHIL-MEM-REALIZE-001.
data StorageRealizationKernelFacts = StorageRealizationKernelFacts
  { storageKernelSubjectBasisAdmitted :: Bool
  , storageKernelExactSubjectPresent :: Bool
  , storageKernelSemanticRevisionNonzero :: Bool
  , storageKernelOutcomeRevisionNonzero :: Bool
  , storageKernelPhysicalStrategyNonzero :: Bool
  , storageKernelSelectedSemanticsNonzero :: Bool
  , storageKernelPhysicalObjectsNonzero :: Bool
  }
  deriving (Eq, Show)

data StorageRealizationCertificationError
  = StorageRealizationCertificationNativeError StorageRealizationError
  | StorageRealizationCertificationKernelDisagreement
      StorageRealizationKernelFacts
  deriving (Eq, Show)

-- | Preserve the unchanged native diagnostic ordering, then require the exact
-- extracted MEM-001 classifier on every native-success path.
checkStorageRealizationCertified
  :: StorageRealizationRelation
  -> Either StorageRealizationCertificationError CheckedStorageRealization
checkStorageRealizationCertified relation = do
  checked <- mapLeft StorageRealizationCertificationNativeError $
    checkStorageRealization relation
  verifyStorageRealizationKernelFacts (storageRealizationKernelFacts relation)
  pure checked

verifyStorageRealizationKernelFacts
  :: StorageRealizationKernelFacts
  -> Either StorageRealizationCertificationError ()
verifyStorageRealizationKernelFacts facts =
  if kernelAccepts facts
    then Right ()
    else Left (StorageRealizationCertificationKernelDisagreement facts)

storageRealizationKernelFacts
  :: StorageRealizationRelation
  -> StorageRealizationKernelFacts
storageRealizationKernelFacts relation =
  StorageRealizationKernelFacts
    { storageKernelSubjectBasisAdmitted = exactSubjectPresent
    , storageKernelExactSubjectPresent = exactSubjectPresent
    , storageKernelSemanticRevisionNonzero = not $ Text.null $
        unStorageSemanticRevision (storageRelationSourceSemanticRevision relation)
    , storageKernelOutcomeRevisionNonzero = not $ Text.null $
        unStorageOutcomeRevision (storageRelationSourceOutcomeRevision relation)
    , storageKernelPhysicalStrategyNonzero = not $ Text.null $
        unPhysicalStorageStrategy (storageRelationPhysicalStrategy relation)
    , storageKernelSelectedSemanticsNonzero = not $ Text.null $
        unRealizationRevision (storageRelationRealizationRevision relation)
    , storageKernelPhysicalObjectsNonzero = all
        (not . Text.null . unPhysicalStorageObjectKey)
        (Set.toAscList (storageRelationPhysicalObjects relation))
    }
  where
    exactSubjectPresent = case storageRelationSubject relation of
      ExactStorageSemanticSubject _ -> True
      PhysicalStorageCoincidence _ -> False

kernelAccepts :: StorageRealizationKernelFacts -> Bool
kernelAccepts facts = Kernel.decideStorageRealizationValidByFacts
  (storageKernelSubjectBasisAdmitted facts)
  (storageKernelExactSubjectPresent facts)
  (storageKernelSemanticRevisionNonzero facts)
  (storageKernelOutcomeRevisionNonzero facts)
  (storageKernelPhysicalStrategyNonzero facts)
  (storageKernelSelectedSemanticsNonzero facts)
  (storageKernelPhysicalObjectsNonzero facts)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
