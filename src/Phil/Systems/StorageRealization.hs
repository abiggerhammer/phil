{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.StorageRealization
  ( SemanticValueKey (..)
  , SemanticStorageResourceKey (..)
  , PhysicalStorageObjectKey (..)
  , PhysicalStorageStrategy (..)
  , StorageSemanticRevision (..)
  , StorageOutcomeRevision (..)
  , StorageFailureKey (..)
  , StorageCapacityEvidenceKey (..)
  , StorageAssumptionKey (..)
  , StorageDeploymentRequirementKey (..)
  , StorageTerminalDispositionKey (..)
  , StorageProfileRevision (..)
  , StorageResidencyRef (..)
  , StorageCleanupRef (..)
  , StorageSemanticSubject (..)
  , StorageSubjectBinding (..)
  , SourceStorageFailureSurface (..)
  , StorageFailureDisposition (..)
  , PhysicalAllocationFailure (..)
  , StorageRealizationRelation (..)
  , CheckedStorageRealization
  , StorageSemanticIdentity (..)
  , SemanticStorageOwnerState (..)
  , SemanticStorageOwner (..)
  , PhysicalStorageState (..)
  , PhysicalStorageObjectState (..)
  , StorageReclamationPolicy (..)
  , StorageCostLineage (..)
  , CheckedStorageCostLineage
  , StorageRealizationError (..)
  , checkStorageRealization
  , checkedStorageSemanticIdentity
  , checkedStoragePhysicalStrategy
  , checkedStoragePhysicalObjects
  , checkEquivalentStorageRealizations
  , checkSemanticStorageTerminalClosure
  , checkPhysicalStorageReclamation
  , checkStorageCostLineage
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static (RealizationRevision (..))
import Phil.Systems.IR (CostClass, CostShape (..))

newtype SemanticValueKey = SemanticValueKey
  { unSemanticValueKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype SemanticStorageResourceKey = SemanticStorageResourceKey
  { unSemanticStorageResourceKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype PhysicalStorageObjectKey = PhysicalStorageObjectKey
  { unPhysicalStorageObjectKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype PhysicalStorageStrategy = PhysicalStorageStrategy
  { unPhysicalStorageStrategy :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageSemanticRevision = StorageSemanticRevision
  { unStorageSemanticRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageOutcomeRevision = StorageOutcomeRevision
  { unStorageOutcomeRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageFailureKey = StorageFailureKey
  { unStorageFailureKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageCapacityEvidenceKey = StorageCapacityEvidenceKey
  { unStorageCapacityEvidenceKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageAssumptionKey = StorageAssumptionKey
  { unStorageAssumptionKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageDeploymentRequirementKey = StorageDeploymentRequirementKey
  { unStorageDeploymentRequirementKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageTerminalDispositionKey = StorageTerminalDispositionKey
  { unStorageTerminalDispositionKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageProfileRevision = StorageProfileRevision
  { unStorageProfileRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageResidencyRef = StorageResidencyRef
  { unStorageResidencyRef :: Text
  }
  deriving (Eq, Ord, Show)

newtype StorageCleanupRef = StorageCleanupRef
  { unStorageCleanupRef :: Text
  }
  deriving (Eq, Ord, Show)

data StorageSemanticSubject
  = OrdinarySemanticValue SemanticValueKey
  | ExplicitSemanticStorageResource SemanticStorageResourceKey
  deriving (Eq, Ord, Show)

-- | Exact semantic binding and represented-but-invalid physical coincidence are
-- separate constructors so a target address/object identity can never become a
-- semantic value/resource identity merely by being equal at runtime.
data StorageSubjectBinding
  = ExactStorageSemanticSubject StorageSemanticSubject
  | PhysicalStorageCoincidence PhysicalStorageObjectKey
  deriving (Eq, Ord, Show)

data SourceStorageFailureSurface
  = SourceStorageInfallible
  | SourceStorageFailures (Set StorageFailureKey)
  deriving (Eq, Ord, Show)

data StorageFailureDisposition
  = StorageFailureMapsToSource StorageFailureKey
  | StorageFailureProvedUnreachable StorageCapacityEvidenceKey
  | StorageFailureAssumption StorageAssumptionKey
  | StorageFailureDeploymentRequirement StorageDeploymentRequirementKey
  | StorageFailureUnaccounted
  deriving (Eq, Ord, Show)

data PhysicalAllocationFailure
  = PhysicalAllocationCannotFail
  | PhysicalAllocationMayFail StorageFailureDisposition
  deriving (Eq, Ord, Show)

-- | Target storage realization for one exact source semantic identity/outcome
-- surface. The strategy/object/revision coordinates are realization metadata;
-- they deliberately do not participate in StorageSemanticIdentity below.
data StorageRealizationRelation = StorageRealizationRelation
  { storageRelationSubject :: StorageSubjectBinding
  , storageRelationSourceSemanticRevision :: StorageSemanticRevision
  , storageRelationSourceOutcomeRevision :: StorageOutcomeRevision
  , storageRelationPhysicalStrategy :: PhysicalStorageStrategy
  , storageRelationPhysicalObjects :: Set PhysicalStorageObjectKey
  , storageRelationRealizationRevision :: RealizationRevision
  , storageRelationSourceFailureSurface :: SourceStorageFailureSurface
  , storageRelationAllocationFailure :: PhysicalAllocationFailure
  }
  deriving (Eq, Ord, Show)

newtype CheckedStorageRealization = CheckedStorageRealization
  { unCheckedStorageRealization :: StorageRealizationRelation
  }
  deriving (Eq, Ord, Show)

data StorageSemanticIdentity = StorageSemanticIdentity
  { storageIdentitySubject :: StorageSemanticSubject
  , storageIdentitySemanticRevision :: StorageSemanticRevision
  , storageIdentityOutcomeRevision :: StorageOutcomeRevision
  }
  deriving (Eq, Ord, Show)

data SemanticStorageOwnerState
  = SemanticStorageOwnerLive
  | SemanticStorageOwnerReleased
  | SemanticStorageOwnerTerminalDisposition StorageTerminalDispositionKey
  deriving (Eq, Ord, Show)

data SemanticStorageOwner = SemanticStorageOwner
  { semanticStorageOwnerKey :: SemanticStorageResourceKey
  , semanticStorageOwnerState :: SemanticStorageOwnerState
  }
  deriving (Eq, Ord, Show)

data PhysicalStorageState
  = PhysicalStorageReclaimed
  | PhysicalStorageRetainedByProfile StorageProfileRevision
  | PhysicalStorageLeaked
  deriving (Eq, Ord, Show)

data PhysicalStorageObjectState = PhysicalStorageObjectState
  { physicalStorageStateObject :: PhysicalStorageObjectKey
  , physicalStorageState :: PhysicalStorageState
  }
  deriving (Eq, Ord, Show)

data StorageReclamationPolicy
  = RequirePhysicalReclamation
  | PermitPhysicalRetention StorageProfileRevision
  deriving (Eq, Ord, Show)

data StorageCostLineage = StorageCostLineage
  { storageCostSubject :: StorageSemanticSubject
  , storageCostPhysicalObjects :: Set PhysicalStorageObjectKey
  , storageCostClass :: CostClass
  , storageCostShape :: CostShape
  , storageCostResidencyRefs :: Set StorageResidencyRef
  , storageCostCleanupRefs :: Set StorageCleanupRef
  }
  deriving (Eq, Ord, Show)

newtype CheckedStorageCostLineage = CheckedStorageCostLineage StorageCostLineage
  deriving (Eq, Ord, Show)

data StorageRealizationError
  = StoragePhysicalCoincidenceIsNotSemanticIdentity PhysicalStorageObjectKey
  | StorageMissingIdentity Text
  | StorageFailureNotDeclared StorageFailureKey
  | StorageUnaccountedAllocationFailure
  | StorageSemanticIdentityMismatch StorageSemanticIdentity StorageSemanticIdentity
  | DuplicateSemanticStorageOwner SemanticStorageResourceKey
  | LiveSemanticStorageOwner SemanticStorageResourceKey
  | UnpermittedSemanticStorageTerminalDisposition
      SemanticStorageResourceKey StorageTerminalDispositionKey
  | DuplicatePhysicalStorageObject PhysicalStorageObjectKey
  | PhysicalStorageLeak PhysicalStorageObjectKey
  | PhysicalStorageRetentionNotPermitted
      PhysicalStorageObjectKey StorageProfileRevision
  | PhysicalStorageRetentionProfileMismatch
      PhysicalStorageObjectKey StorageProfileRevision StorageProfileRevision
  | StorageCostSubjectMismatch StorageSemanticSubject StorageSemanticSubject
  | StorageCostPhysicalDomainMismatch
      (Set PhysicalStorageObjectKey) (Set PhysicalStorageObjectKey)
  | StorageCostHasNoAttributableStorageFact
  deriving (Eq, Ord, Show)

checkStorageRealization
  :: StorageRealizationRelation
  -> Either StorageRealizationError CheckedStorageRealization
checkStorageRealization relation = do
  case storageRelationSubject relation of
    ExactStorageSemanticSubject exactSubject -> validateSubject exactSubject
    PhysicalStorageCoincidence object ->
      Left (StoragePhysicalCoincidenceIsNotSemanticIdentity object)
  validateText "source semantic revision"
    (unStorageSemanticRevision (storageRelationSourceSemanticRevision relation))
  validateText "source outcome revision"
    (unStorageOutcomeRevision (storageRelationSourceOutcomeRevision relation))
  validateText "physical storage strategy"
    (unPhysicalStorageStrategy (storageRelationPhysicalStrategy relation))
  validateText "architecture realization revision"
    (unRealizationRevision (storageRelationRealizationRevision relation))
  mapM_ validatePhysicalObject (Set.toAscList (storageRelationPhysicalObjects relation))
  validateFailureDisposition
    (storageRelationSourceFailureSurface relation)
    (storageRelationAllocationFailure relation)
  Right (CheckedStorageRealization relation)

checkedStorageSemanticIdentity :: CheckedStorageRealization -> StorageSemanticIdentity
checkedStorageSemanticIdentity checked = StorageSemanticIdentity
  { storageIdentitySubject = exactSubject
  , storageIdentitySemanticRevision = storageRelationSourceSemanticRevision relation
  , storageIdentityOutcomeRevision = storageRelationSourceOutcomeRevision relation
  }
  where
    relation = unCheckedStorageRealization checked
    exactSubject = case storageRelationSubject relation of
      ExactStorageSemanticSubject subject -> subject
      PhysicalStorageCoincidence _ ->
        error "checked storage realization retained physical coincidence"

checkedStoragePhysicalStrategy :: CheckedStorageRealization -> PhysicalStorageStrategy
checkedStoragePhysicalStrategy =
  storageRelationPhysicalStrategy . unCheckedStorageRealization

checkedStoragePhysicalObjects
  :: CheckedStorageRealization
  -> Set PhysicalStorageObjectKey
checkedStoragePhysicalObjects =
  storageRelationPhysicalObjects . unCheckedStorageRealization

checkEquivalentStorageRealizations
  :: CheckedStorageRealization
  -> CheckedStorageRealization
  -> Either StorageRealizationError ()
checkEquivalentStorageRealizations first second
  | firstIdentity == secondIdentity = Right ()
  | otherwise = Left (StorageSemanticIdentityMismatch firstIdentity secondIdentity)
  where
    firstIdentity = checkedStorageSemanticIdentity first
    secondIdentity = checkedStorageSemanticIdentity second

checkSemanticStorageTerminalClosure
  :: Map SemanticStorageResourceKey (Set StorageTerminalDispositionKey)
  -> [SemanticStorageOwner]
  -> Either StorageRealizationError ()
checkSemanticStorageTerminalClosure permitted = go Set.empty
  where
    go _ [] = Right ()
    go seen (owner : rest) = do
      let key = semanticStorageOwnerKey owner
      validateText "semantic storage resource" (unSemanticStorageResourceKey key)
      if Set.member key seen
        then Left (DuplicateSemanticStorageOwner key)
        else checkOwner key (semanticStorageOwnerState owner)
      go (Set.insert key seen) rest

    checkOwner key state = case state of
      SemanticStorageOwnerLive -> Left (LiveSemanticStorageOwner key)
      SemanticStorageOwnerReleased -> Right ()
      SemanticStorageOwnerTerminalDisposition disposition -> do
        validateText "semantic storage terminal disposition"
          (unStorageTerminalDispositionKey disposition)
        if Set.member disposition (Map.findWithDefault Set.empty key permitted)
          then Right ()
          else Left (UnpermittedSemanticStorageTerminalDisposition key disposition)

checkPhysicalStorageReclamation
  :: StorageReclamationPolicy
  -> [PhysicalStorageObjectState]
  -> Either StorageRealizationError ()
checkPhysicalStorageReclamation policy = go Set.empty
  where
    go _ [] = Right ()
    go seen (objectState : rest) = do
      let object = physicalStorageStateObject objectState
      validatePhysicalObject object
      if Set.member object seen
        then Left (DuplicatePhysicalStorageObject object)
        else checkState object (physicalStorageState objectState)
      go (Set.insert object seen) rest

    checkState object state = case state of
      PhysicalStorageReclaimed -> Right ()
      PhysicalStorageLeaked -> Left (PhysicalStorageLeak object)
      PhysicalStorageRetainedByProfile actualProfile -> do
        validateProfile actualProfile
        case policy of
          RequirePhysicalReclamation ->
            Left (PhysicalStorageRetentionNotPermitted object actualProfile)
          PermitPhysicalRetention expectedProfile -> do
            validateProfile expectedProfile
            if expectedProfile == actualProfile
              then Right ()
              else Left (PhysicalStorageRetentionProfileMismatch
                object expectedProfile actualProfile)

checkStorageCostLineage
  :: CheckedStorageRealization
  -> StorageCostLineage
  -> Either StorageRealizationError CheckedStorageCostLineage
checkStorageCostLineage checked lineage = do
  let expectedSubject = storageIdentitySubject (checkedStorageSemanticIdentity checked)
      actualSubject = storageCostSubject lineage
      expectedObjects = checkedStoragePhysicalObjects checked
      actualObjects = storageCostPhysicalObjects lineage
  validateSubject actualSubject
  mapM_ validatePhysicalObject (Set.toAscList actualObjects)
  if expectedSubject == actualSubject
    then Right ()
    else Left (StorageCostSubjectMismatch expectedSubject actualSubject)
  if expectedObjects == actualObjects
    then Right ()
    else Left (StorageCostPhysicalDomainMismatch expectedObjects actualObjects)
  mapM_ (validateText "storage residency cost reference" . unStorageResidencyRef)
    (Set.toAscList (storageCostResidencyRefs lineage))
  mapM_ (validateText "storage cleanup cost reference" . unStorageCleanupRef)
    (Set.toAscList (storageCostCleanupRefs lineage))
  if hasAttributableStorageCost lineage
    then Right (CheckedStorageCostLineage lineage)
    else Left StorageCostHasNoAttributableStorageFact

validateFailureDisposition
  :: SourceStorageFailureSurface
  -> PhysicalAllocationFailure
  -> Either StorageRealizationError ()
validateFailureDisposition _ PhysicalAllocationCannotFail = Right ()
validateFailureDisposition sourceSurface (PhysicalAllocationMayFail disposition) =
  case disposition of
    StorageFailureMapsToSource failure -> do
      validateText "source storage failure" (unStorageFailureKey failure)
      if sourceFailureContains failure sourceSurface
        then Right ()
        else Left (StorageFailureNotDeclared failure)
    StorageFailureProvedUnreachable evidence ->
      validateText "storage capacity evidence" (unStorageCapacityEvidenceKey evidence)
    StorageFailureAssumption assumption ->
      validateText "storage allocation assumption" (unStorageAssumptionKey assumption)
    StorageFailureDeploymentRequirement requirement ->
      validateText "storage deployment requirement"
        (unStorageDeploymentRequirementKey requirement)
    StorageFailureUnaccounted -> Left StorageUnaccountedAllocationFailure

sourceFailureContains :: StorageFailureKey -> SourceStorageFailureSurface -> Bool
sourceFailureContains _ SourceStorageInfallible = False
sourceFailureContains failure (SourceStorageFailures failures) = Set.member failure failures

validateSubject :: StorageSemanticSubject -> Either StorageRealizationError ()
validateSubject subject = case subject of
  OrdinarySemanticValue key ->
    validateText "ordinary semantic value" (unSemanticValueKey key)
  ExplicitSemanticStorageResource key ->
    validateText "semantic storage resource" (unSemanticStorageResourceKey key)

validatePhysicalObject :: PhysicalStorageObjectKey -> Either StorageRealizationError ()
validatePhysicalObject =
  validateText "physical storage object" . unPhysicalStorageObjectKey

validateProfile :: StorageProfileRevision -> Either StorageRealizationError ()
validateProfile = validateText "storage profile revision" . unStorageProfileRevision

validateText :: Text -> Text -> Either StorageRealizationError ()
validateText label value
  | Text.null value = Left (StorageMissingIdentity label)
  | otherwise = Right ()

hasAttributableStorageCost :: StorageCostLineage -> Bool
hasAttributableStorageCost lineage =
  or
    [ isJust (costAllocationCount shape)
    , isJust (costPeakLiveMemory shape)
    , isJust (costBytesCopied shape)
    , not (Set.null (storageCostResidencyRefs lineage))
    , not (Set.null (storageCostCleanupRefs lineage))
    ]
  where
    shape = storageCostShape lineage
