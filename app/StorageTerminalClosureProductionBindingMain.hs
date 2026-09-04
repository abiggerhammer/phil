{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Process
import Phil.Core.ProcessLifecycle
import Phil.Core.Protocol (emptyProtocolContext)
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.Examples.Phase1.StageClosureWitnesses (uploadStageClosureBundle)
import Phil.Systems.Storage
import Phil.Systems.StorageTerminalClosureCertification
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "certified semantic closure accepts released owner" releasedOwnerAccepted
    , test "certified semantic closure accepts exact terminal disposition" dispositionAccepted
    , test "native live-owner diagnostic precedes semantic kernel" liveOwnerNativePrecedence
    , test "injected semantic aggregate disagreement fails closed" semanticInjectedDisagreement
    , test "certified physical reclamation accepts reclaimed object" reclaimedAccepted
    , test "certified physical reclamation accepts exact profile retention" retentionAccepted
    , test "native physical-leak diagnostic precedes reclamation kernel" leakNativePrecedence
    , test "injected physical aggregate disagreement fails closed" physicalInjectedDisagreement
    , test "verified StageClosure and refined realization compose process storage gate" processStorageCompositionAccepted
    , test "certified root terminal accepts closed semantic storage" rootStorageClosureAccepted
    , test "live semantic owner blocks certified root terminal" rootLiveOwnerRejected
    , test "physical leak remains separate from semantic root terminal" physicalLeakDoesNotRewriteRoot
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

releasedOwnerAccepted :: Either String ()
releasedOwnerAccepted = mapLeft show $
  checkSemanticStorageTerminalClosureCertified Map.empty [releasedOwner]

dispositionAccepted :: Either String ()
dispositionAccepted = mapLeft show $
  checkSemanticStorageTerminalClosureCertified permittedDispositions [disposedOwner]

liveOwnerNativePrecedence :: Either String ()
liveOwnerNativePrecedence =
  case checkSemanticStorageTerminalClosureCertified Map.empty [liveOwner] of
    Left (StorageTerminalClosureNativeStorageError (LiveSemanticStorageOwner key)) ->
      assert (key == storageKey) "wrong live semantic storage owner"
    other -> Left ("live owner did not preserve native diagnostic precedence: " <> show other)

semanticInjectedDisagreement :: Either String ()
semanticInjectedDisagreement =
  let facts = SemanticStorageClosureKernelFacts
        { semanticStorageOwnerKeysUnique = False
        , semanticStorageOwnersClosed = True
        , semanticStorageOwnerFacts = [SemanticStorageReleasedKernelFacts]
        }
  in case verifySemanticStorageClosureKernelFacts facts of
      Left (StorageTerminalClosureSemanticKernelDisagreement actual) ->
        assert (actual == facts) "semantic disagreement lost reflected facts"
      other -> Left ("semantic disagreement did not fail closed: " <> show other)

reclaimedAccepted :: Either String ()
reclaimedAccepted = mapLeft show $
  checkPhysicalStorageReclamationCertified RequirePhysicalReclamation
    [PhysicalStorageObjectState physicalObject PhysicalStorageReclaimed]

retentionAccepted :: Either String ()
retentionAccepted = mapLeft show $
  checkPhysicalStorageReclamationCertified
    (PermitPhysicalRetention retentionProfile)
    [PhysicalStorageObjectState physicalObject
      (PhysicalStorageRetainedByProfile retentionProfile)]

leakNativePrecedence :: Either String ()
leakNativePrecedence =
  case checkPhysicalStorageReclamationCertified RequirePhysicalReclamation
      [PhysicalStorageObjectState physicalObject PhysicalStorageLeaked] of
    Left (StorageTerminalClosureNativeStorageError (PhysicalStorageLeak object)) ->
      assert (object == physicalObject) "wrong leaked physical object"
    other -> Left ("physical leak did not preserve native diagnostic precedence: " <> show other)

physicalInjectedDisagreement :: Either String ()
physicalInjectedDisagreement =
  let facts = PhysicalStorageReclamationKernelFacts
        { physicalStorageObjectKeysUnique = False
        , physicalStorageStatesAccepted = True
        , physicalStorageStateFacts = [PhysicalStorageReclaimedKernelFacts]
        }
  in case verifyPhysicalStorageReclamationKernelFacts facts of
      Left (StorageTerminalClosurePhysicalKernelDisagreement actual) ->
        assert (actual == facts) "physical disagreement lost reflected facts"
      other -> Left ("physical disagreement did not fail closed: " <> show other)

processStorageCompositionAccepted :: Either String ()
processStorageCompositionAccepted = do
  stage <- uploadStageClosureBundle
  mapLeft show $ certifyMemoryProcessStorageClosure
    stage validStorageRelation Map.empty [releasedOwner]

rootStorageClosureAccepted :: Either String ()
rootStorageClosureAccepted = do
  (terminalState, processA, processB) <- terminalRuntime
  disposition <- mapLeft show $ classifyProcessNetworkWithStorageCertification
    emptyRootClosure [] Map.empty
    (Map.fromList [(processA, [releasedOwner]), (processB, [])])
    terminalState
  case disposition of
    NetworkTerminal _ -> Right ()
    other -> Left ("certified root closure changed terminal classification: " <> show other)

rootLiveOwnerRejected :: Either String ()
rootLiveOwnerRejected = do
  (terminalState, processA, processB) <- terminalRuntime
  case classifyProcessNetworkWithStorageCertification
      emptyRootClosure [] Map.empty
      (Map.fromList [(processA, [liveOwner]), (processB, [])])
      terminalState of
    Left (StorageTerminalClosureRootStorageError actualProcess
      (StorageTerminalClosureNativeStorageError (LiveSemanticStorageOwner key))) -> do
        assert (actualProcess == processA) "root storage error lost process identity"
        assert (key == storageKey) "root storage error lost owner identity"
    other -> Left ("live owner did not block certified root terminal: " <> show other)

physicalLeakDoesNotRewriteRoot :: Either String ()
physicalLeakDoesNotRewriteRoot = do
  (terminalState, processA, processB) <- terminalRuntime
  _ <- mapLeft show $ classifyProcessNetworkWithStorageCertification
    emptyRootClosure [] Map.empty
    (Map.fromList [(processA, [releasedOwner]), (processB, [])])
    terminalState
  case checkPhysicalStorageReclamationCertified RequirePhysicalReclamation
      [PhysicalStorageObjectState physicalObject PhysicalStorageLeaked] of
    Left (StorageTerminalClosureNativeStorageError (PhysicalStorageLeak object)) ->
      assert (object == physicalObject)
        "separate physical reclamation rejection lost physical identity"
    other -> Left ("physical leak unexpectedly passed realization gate: " <> show other)

releasedOwner, disposedOwner, liveOwner :: SemanticStorageOwner
releasedOwner = SemanticStorageOwner storageKey SemanticStorageOwnerReleased
disposedOwner = SemanticStorageOwner storageKey
  (SemanticStorageOwnerTerminalDisposition processExitDisposition)
liveOwner = SemanticStorageOwner storageKey SemanticStorageOwnerLive

permittedDispositions :: Map.Map SemanticStorageResourceKey (Set.Set StorageTerminalDispositionKey)
permittedDispositions = Map.singleton storageKey (Set.singleton processExitDisposition)

validStorageRelation :: StorageRealizationRelation
validStorageRelation = StorageRealizationRelation
  { storageRelationSubject = ExactStorageSemanticSubject
      (ExplicitSemanticStorageResource storageKey)
  , storageRelationSourceSemanticRevision = StorageSemanticRevision "semantic.storage.v1"
  , storageRelationSourceOutcomeRevision = StorageOutcomeRevision "outcome.storage.v1"
  , storageRelationPhysicalStrategy = PhysicalStorageStrategy "qualified-storage"
  , storageRelationPhysicalObjects = Set.empty
  , storageRelationRealizationRevision = RealizationRevision "realization.storage.v1"
  , storageRelationSourceFailureSurface = SourceStorageInfallible
  , storageRelationAllocationFailure = PhysicalAllocationCannotFail
  }

storageKey :: SemanticStorageResourceKey
storageKey = SemanticStorageResourceKey "storage.semantic.001"

processExitDisposition :: StorageTerminalDispositionKey
processExitDisposition = StorageTerminalDispositionKey "storage.process-exit"

physicalObject :: PhysicalStorageObjectKey
physicalObject = PhysicalStorageObjectKey "storage.physical.001"

retentionProfile :: StorageProfileRevision
retentionProfile = StorageProfileRevision "profile.process-exit.v1"

terminalRuntime :: Either String (ProcessRuntimeState, ProcessKey, ProcessKey)
terminalRuntime = do
  before <- baseRuntime
  let (processA, processB) = processKeys (runtimeNetwork before)
  afterA <- mapLeft show $ applyDeclaredTerminalTransition
    (terminalTransition processA) before
  afterB <- mapLeft show $ applyDeclaredTerminalTransition
    (terminalTransition processB) afterA
  Right (afterB, processA, processB)

baseRuntime :: Either String ProcessRuntimeState
baseRuntime = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
  mapLeft show $ initializeProcessRuntime network (Map.fromList
    [ (processA, emptyProtocolContext)
    , (processB, emptyProtocolContext)
    ])

baseNetwork :: Either String ProcessNetwork
baseNetwork = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  mapLeft show $ activateRootProcesses network0

terminalTransition :: ProcessKey -> DeclaredTerminalTransition
terminalTransition processKey = DeclaredTerminalTransition
  { declaredTerminalProcess = processKey
  , declaredTerminalControl = Closed doneOutcome
  , declaredTerminalDisposals = []
  }

emptyRootClosure :: RootClosureState
emptyRootClosure = RootClosureState
  { rootOpenResources = Set.empty
  , rootOpenObligations = Set.empty
  , rootPendingObservables = Set.empty
  }

doneOutcome :: Outcome
doneOutcome = Outcome "done"

processKeys :: ProcessNetwork -> (ProcessKey, ProcessKey)
processKeys network =
  let rootRevision = identityInstanceRevision (processNetworkRoot network)
  in ( deriveProcessKey rootRevision (processSiteKey siteA)
     , deriveProcessKey rootRevision (processSiteKey siteB)
     )

rootGraph :: Either ArchitectureInstantiationError ArchitectureInstanceGraph
rootGraph = instantiateArchitecture rootKey rootSpec

rootSpec :: ArchitectureNodeSpec
rootSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "root"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren =
      [ ArchitectureChildSpec slotA workerSpec
      , ArchitectureChildSpec slotB workerSpec
      ]
  , architectureNodeReferences = []
  }

workerSpec :: ArchitectureNodeSpec
workerSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "worker"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

declaration :: Text -> DeclarationIdentity
declaration label = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation
      { declarationDisplayName = label
      , declarationModulePath = []
      }
  , declarationKey = DeclarationKey ("decl-" <> label)
  , declarationInterfaceSemantics = SemanticAtom "interface"
  , declarationDefinitionSemantics = SemanticAtom "definition"
  }

siteA, siteB :: ProcessDeclarationSite
siteA = ProcessDeclarationSite (ProcessSiteKey "site-a") targetA
siteB = ProcessDeclarationSite (ProcessSiteKey "site-b") targetB

rootKey, targetA, targetB :: InstanceKey
rootKey = InstanceKey "root-instance"
targetA = scopedInstanceKey rootKey slotA
targetB = scopedInstanceKey rootKey slotB

slotA, slotB :: OccurrenceSlotKey
slotA = OccurrenceSlotKey "worker-a"
slotB = OccurrenceSlotKey "worker-b"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
