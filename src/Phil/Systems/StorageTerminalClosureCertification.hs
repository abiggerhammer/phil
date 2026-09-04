module Phil.Systems.StorageTerminalClosureCertification
  ( SemanticStorageOwnerKernelFacts (..)
  , SemanticStorageClosureKernelFacts (..)
  , PhysicalStorageStateKernelFacts (..)
  , PhysicalStorageReclamationKernelFacts (..)
  , StorageTerminalClosureCertificationError (..)
  , ProcessStoragePermissions
  , ProcessStorageOwners
  , semanticStorageClosureKernelFacts
  , physicalStorageReclamationKernelFacts
  , verifySemanticStorageClosureKernelFacts
  , verifyPhysicalStorageReclamationKernelFacts
  , checkSemanticStorageTerminalClosureCertified
  , checkPhysicalStorageReclamationCertified
  , certifyMemoryProcessStorageClosure
  , classifyProcessNetworkWithStorageCertification
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Core.Process (ProcessKey, ProcessNetwork (..))
import Phil.Core.ProcessLifecycle
  ( EnabledProcessTransition
  , ProcessLifecycleError
  , ProcessNetworkDisposition (..)
  , ProcessRuntimeState (..)
  , RootClosureState
  , classifyProcessNetwork
  )
import Phil.Systems.StageClosure
  ( StageClosureBundle
  , StageClosureVerificationError
  , verifyStageClosureBundle
  )
import Phil.Systems.Storage
import Phil.Systems.StorageRealizationCertification
  ( StorageRealizationCertificationError
  , checkStorageRealizationCertified
  )
import qualified StorageTerminalClosureKernel as Kernel

-- | Per-owner facts for the exact Certified SemanticStorageOwnerClosed cases.
data SemanticStorageOwnerKernelFacts
  = SemanticStorageLiveKernelFacts
  | SemanticStorageReleasedKernelFacts
  | SemanticStorageTerminalDispositionKernelFacts
      { semanticStorageDispositionPermittedExact :: Bool
      }
  deriving (Eq, Show)

-- | Reflection of NoDup owner keys and Forall owner closure.
data SemanticStorageClosureKernelFacts = SemanticStorageClosureKernelFacts
  { semanticStorageOwnerKeysUnique :: Bool
  , semanticStorageOwnersClosed :: Bool
  , semanticStorageOwnerFacts :: [SemanticStorageOwnerKernelFacts]
  }
  deriving (Eq, Show)

-- | Per-object facts for the exact Certified PhysicalStorageStateAccepted cases.
data PhysicalStorageStateKernelFacts
  = PhysicalStorageReclaimedKernelFacts
  | PhysicalStorageLeakedKernelFacts
  | PhysicalStorageRetainedKernelFacts
      { physicalStoragePolicyPermitsRetention :: Bool
      , physicalStorageProfileExact :: Bool
      }
  deriving (Eq, Show)

-- | Reflection of NoDup physical keys and Forall accepted physical states.
data PhysicalStorageReclamationKernelFacts = PhysicalStorageReclamationKernelFacts
  { physicalStorageObjectKeysUnique :: Bool
  , physicalStorageStatesAccepted :: Bool
  , physicalStorageStateFacts :: [PhysicalStorageStateKernelFacts]
  }
  deriving (Eq, Show)

type ProcessStoragePermissions =
  Map ProcessKey (Map SemanticStorageResourceKey (Set StorageTerminalDispositionKey))

type ProcessStorageOwners = Map ProcessKey [SemanticStorageOwner]

data StorageTerminalClosureCertificationError
  = StorageTerminalClosureNativeStorageError StorageRealizationError
  | StorageTerminalClosureSemanticKernelDisagreement
      SemanticStorageClosureKernelFacts
  | StorageTerminalClosurePhysicalKernelDisagreement
      PhysicalStorageReclamationKernelFacts
  | StorageTerminalClosureStageError StageClosureVerificationError
  | StorageTerminalClosureRealizationError StorageRealizationCertificationError
  | StorageTerminalClosureProcessKernelDisagreement
  | StorageTerminalClosureRootNativeError ProcessLifecycleError
  | StorageTerminalClosureRootPopulationMismatch
      (Set ProcessKey) (Set ProcessKey)
  | StorageTerminalClosureRootStorageError
      ProcessKey StorageTerminalClosureCertificationError
  | StorageTerminalClosureRootKernelDisagreement
  deriving (Eq, Show)

checkSemanticStorageTerminalClosureCertified
  :: Map SemanticStorageResourceKey (Set StorageTerminalDispositionKey)
  -> [SemanticStorageOwner]
  -> Either StorageTerminalClosureCertificationError ()
checkSemanticStorageTerminalClosureCertified permitted owners = do
  mapLeft StorageTerminalClosureNativeStorageError $
    checkSemanticStorageTerminalClosure permitted owners
  verifySemanticStorageClosureKernelFacts
    (semanticStorageClosureKernelFacts permitted owners)

checkPhysicalStorageReclamationCertified
  :: StorageReclamationPolicy
  -> [PhysicalStorageObjectState]
  -> Either StorageTerminalClosureCertificationError ()
checkPhysicalStorageReclamationCertified policy objects = do
  mapLeft StorageTerminalClosureNativeStorageError $
    checkPhysicalStorageReclamation policy objects
  verifyPhysicalStorageReclamationKernelFacts
    (physicalStorageReclamationKernelFacts policy objects)

semanticStorageClosureKernelFacts
  :: Map SemanticStorageResourceKey (Set StorageTerminalDispositionKey)
  -> [SemanticStorageOwner]
  -> SemanticStorageClosureKernelFacts
semanticStorageClosureKernelFacts permitted owners =
  SemanticStorageClosureKernelFacts
    { semanticStorageOwnerKeysUnique = unique keys
    , semanticStorageOwnersClosed = all semanticOwnerKernelAccepts ownerFacts
    , semanticStorageOwnerFacts = ownerFacts
    }
  where
    keys = map semanticStorageOwnerKey owners
    ownerFacts = map (semanticOwnerKernelFacts permitted) owners

physicalStorageReclamationKernelFacts
  :: StorageReclamationPolicy
  -> [PhysicalStorageObjectState]
  -> PhysicalStorageReclamationKernelFacts
physicalStorageReclamationKernelFacts policy objects =
  PhysicalStorageReclamationKernelFacts
    { physicalStorageObjectKeysUnique = unique keys
    , physicalStorageStatesAccepted = all physicalStateKernelAccepts stateFacts
    , physicalStorageStateFacts = stateFacts
    }
  where
    keys = map physicalStorageStateObject objects
    stateFacts = map (physicalStateKernelFacts policy) objects

verifySemanticStorageClosureKernelFacts
  :: SemanticStorageClosureKernelFacts
  -> Either StorageTerminalClosureCertificationError ()
verifySemanticStorageClosureKernelFacts facts
  | all semanticOwnerKernelAccepts (semanticStorageOwnerFacts facts)
      && Kernel.decideSemanticStorageClosureByFacts
        (semanticStorageOwnerKeysUnique facts)
        (semanticStorageOwnersClosed facts) = Right ()
  | otherwise = Left (StorageTerminalClosureSemanticKernelDisagreement facts)

verifyPhysicalStorageReclamationKernelFacts
  :: PhysicalStorageReclamationKernelFacts
  -> Either StorageTerminalClosureCertificationError ()
verifyPhysicalStorageReclamationKernelFacts facts
  | all physicalStateKernelAccepts (physicalStorageStateFacts facts)
      && Kernel.decidePhysicalStorageReclamationByFacts
        (physicalStorageObjectKeysUnique facts)
        (physicalStorageStatesAccepted facts) = Right ()
  | otherwise = Left (StorageTerminalClosurePhysicalKernelDisagreement facts)

-- | Compose the three storage-specific fields of CertifiedMemoryProcessClosure
-- from real production predecessors. Ordinary process-terminal certification
-- remains the separate process-lifecycle predecessor carried by the theorem's
-- CertifiedProcessTerminalFact parameter.
certifyMemoryProcessStorageClosure
  :: StageClosureBundle
  -> StorageRealizationRelation
  -> Map SemanticStorageResourceKey (Set StorageTerminalDispositionKey)
  -> [SemanticStorageOwner]
  -> Either StorageTerminalClosureCertificationError ()
certifyMemoryProcessStorageClosure stage relation permitted owners = do
  mapLeft StorageTerminalClosureStageError $ verifyStageClosureBundle stage
  _ <- mapLeft StorageTerminalClosureRealizationError $
    checkStorageRealizationCertified relation
  checkSemanticStorageTerminalClosureCertified permitted owners
  if Kernel.decideCertifiedMemoryProcessClosureByFacts True True True
    then Right ()
    else Left StorageTerminalClosureProcessKernelDisagreement

-- | Preserve native process/root terminal diagnostics first. Only when native
-- classification establishes NetworkTerminal do semantic storage owners become
-- an additional terminal-closure requirement. Physical reclamation is
-- intentionally absent from this API and from the extracted root gate.
classifyProcessNetworkWithStorageCertification
  :: RootClosureState
  -> [EnabledProcessTransition]
  -> ProcessStoragePermissions
  -> ProcessStorageOwners
  -> ProcessRuntimeState
  -> Either StorageTerminalClosureCertificationError ProcessNetworkDisposition
classifyProcessNetworkWithStorageCertification rootClosure enabled permissions owners state = do
  disposition <- mapLeft StorageTerminalClosureRootNativeError $
    classifyProcessNetwork rootClosure enabled state
  case disposition of
    NetworkTerminal _ -> do
      let population = Map.keysSet (processNetworkPopulation (runtimeNetwork state))
          statuses = Map.keysSet (runtimeStatuses state)
      if population == statuses
        then Right ()
        else Left (StorageTerminalClosureRootPopulationMismatch population statuses)
      mapM_ certifyProcessStorage (Set.toAscList population)
      if Kernel.decideCertifiedMemoryRootClosureByFacts True True
        then Right disposition
        else Left StorageTerminalClosureRootKernelDisagreement
    _ -> Right disposition
  where
    certifyProcessStorage processKey =
      mapLeft (StorageTerminalClosureRootStorageError processKey) $
        checkSemanticStorageTerminalClosureCertified
          (Map.findWithDefault Map.empty processKey permissions)
          (Map.findWithDefault [] processKey owners)

semanticOwnerKernelFacts
  :: Map SemanticStorageResourceKey (Set StorageTerminalDispositionKey)
  -> SemanticStorageOwner
  -> SemanticStorageOwnerKernelFacts
semanticOwnerKernelFacts permitted owner =
  case semanticStorageOwnerState owner of
    SemanticStorageOwnerLive -> SemanticStorageLiveKernelFacts
    SemanticStorageOwnerReleased -> SemanticStorageReleasedKernelFacts
    SemanticStorageOwnerTerminalDisposition disposition ->
      SemanticStorageTerminalDispositionKernelFacts
        (Set.member disposition
          (Map.findWithDefault Set.empty (semanticStorageOwnerKey owner) permitted))

semanticOwnerKernelAccepts :: SemanticStorageOwnerKernelFacts -> Bool
semanticOwnerKernelAccepts facts = case facts of
  SemanticStorageLiveKernelFacts -> Kernel.decideSemanticStorageLiveByFacts
  SemanticStorageReleasedKernelFacts -> Kernel.decideSemanticStorageReleasedByFacts
  SemanticStorageTerminalDispositionKernelFacts permittedExact ->
    Kernel.decideSemanticStorageTerminalDispositionByFacts permittedExact

physicalStateKernelFacts
  :: StorageReclamationPolicy
  -> PhysicalStorageObjectState
  -> PhysicalStorageStateKernelFacts
physicalStateKernelFacts policy objectState =
  case physicalStorageState objectState of
    PhysicalStorageReclaimed -> PhysicalStorageReclaimedKernelFacts
    PhysicalStorageLeaked -> PhysicalStorageLeakedKernelFacts
    PhysicalStorageRetainedByProfile actualProfile ->
      PhysicalStorageRetainedKernelFacts
        { physicalStoragePolicyPermitsRetention = case policy of
            RequirePhysicalReclamation -> False
            PermitPhysicalRetention _ -> True
        , physicalStorageProfileExact = case policy of
            RequirePhysicalReclamation -> False
            PermitPhysicalRetention expectedProfile -> expectedProfile == actualProfile
        }

physicalStateKernelAccepts :: PhysicalStorageStateKernelFacts -> Bool
physicalStateKernelAccepts facts = case facts of
  PhysicalStorageReclaimedKernelFacts ->
    Kernel.decidePhysicalStorageReclaimedByFacts
  PhysicalStorageLeakedKernelFacts ->
    Kernel.decidePhysicalStorageLeakedByFacts
  PhysicalStorageRetainedKernelFacts permits exactProfile ->
    Kernel.decidePhysicalStorageRetainedByProfileByFacts permits exactProfile

unique :: Ord a => [a] -> Bool
unique values = length values == Set.size (Set.fromList values)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
