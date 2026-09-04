{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ConcurrencyRendezvousCertification
import Phil.Core.ConcurrencyTerminalCertification
import Phil.Core.Process
import Phil.Core.ProcessActivation (ProcessActivationContract (..))
import Phil.Core.ProcessLifecycle
import Phil.Core.Protocol (emptyProtocolContext)
import Phil.Core.Static
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "certified declared Closed transition accepts" declaredClosedAccepts
    , test "native-success Return transition fails closed at terminal kernel" returnFailsClosed
    , test "native Continue rejection preserves diagnostic precedence" continueNativePrecedence
    , test "certified fatal transition preserves peer state" fatalIsolationAccepts
    , test "injected process-terminal kernel disagreement fails closed" processKernelDisagreementRejects
    , test "injected failure-isolation kernel disagreement fails closed" failureKernelDisagreementRejects
    , test "all certified process facts close exact root" rootTerminalAccepts
    , test "root semantic residue preserves native diagnostic precedence" rootResidueNativePrecedence
    , test "injected root-terminal kernel disagreement fails closed" rootKernelDisagreementRejects
    , test "running process with no enabled semantic step is certified stuck" stuckAccepts
    , test "certified local enabled step produces can-step disposition" enabledLocalCanStep
    , test "terminal process cannot be certified as locally enabled" terminalEnabledRejects
    , test "injected stuck kernel disagreement fails closed" stuckKernelDisagreementRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

declaredClosedAccepts :: Either String ()
declaredClosedAccepts = do
  runtime <- baseRuntime
  let (processA, _) = processKeys (runtimeNetwork (certifiedTerminalRuntimeState runtime))
  after <- mapLeft show $ applyDeclaredTerminalTransitionCertified
    (terminalTransition processA (Closed doneOutcome)) runtime
  case Map.lookup processA (runtimeStatuses (certifiedTerminalRuntimeState after)) of
    Just (ProcessTerminal fact) ->
      assert (terminalFactControl fact == Closed doneOutcome)
        "certified declared terminal fact changed exact outcome"
    other -> Left ("certified declared transition did not terminate actor: " <> show other)

returnFailsClosed :: Either String ()
returnFailsClosed = do
  runtime <- baseRuntime
  let (processA, _) = processKeys (runtimeNetwork (certifiedTerminalRuntimeState runtime))
  case applyDeclaredTerminalTransitionCertified
      (terminalTransition processA (Return TyUnit)) runtime of
    Left (ConcurrencyTerminalProcessKernelDisagreement facts) ->
      assert (not (terminalControlExact facts))
        "Return rejection did not retain exact terminal-control disagreement"
    other -> Left ("native-success Return crossed Certified terminal boundary: " <> show other)

continueNativePrecedence :: Either String ()
continueNativePrecedence = do
  runtime <- baseRuntime
  let (processA, _) = processKeys (runtimeNetwork (certifiedTerminalRuntimeState runtime))
  case applyDeclaredTerminalTransitionCertified
      (terminalTransition processA Continue) runtime of
    Left (ConcurrencyTerminalNativeError (TerminalContinueRejected actual)) ->
      assert (actual == processA) "Continue rejection lost exact ProcessKey"
    other -> Left ("Continue did not preserve native diagnostic precedence: " <> show other)

fatalIsolationAccepts :: Either String ()
fatalIsolationAccepts = do
  runtime <- baseRuntime
  let state = certifiedTerminalRuntimeState runtime
      (actor, peer) = processKeys (runtimeNetwork state)
      peerBefore = Map.lookup peer (runtimeStatuses state)
  after <- mapLeft show $ applyFatalProcessTransitionCertified
    FatalProcessTransition
      { fatalTransitionProcess = actor
      , fatalTransitionClass = "fatal.production"
      , fatalTransitionDetail = "boom"
      , fatalTransitionDisposals = []
      }
    runtime
  assert
    (Map.lookup peer (runtimeStatuses (certifiedTerminalRuntimeState after)) == peerBefore)
    "certified fatal transition changed peer status"

processKernelDisagreementRejects :: Either String ()
processKernelDisagreementRejects =
  case verifyProcessTerminalKernelFacts
      (ProcessTerminalKernelFacts True True False True) of
    Left (ConcurrencyTerminalProcessKernelDisagreement facts) ->
      assert (not (terminalEndpointsClosed facts))
        "process kernel disagreement lost endpoint fact"
    other -> Left ("process kernel disagreement did not fail closed: " <> show other)

failureKernelDisagreementRejects :: Either String ()
failureKernelDisagreementRejects =
  case verifyFailureIsolationKernelFacts
      (FailureIsolationKernelFacts True True False) of
    Left (ConcurrencyTerminalFailureKernelDisagreement facts) ->
      assert (not (failurePeersUnchanged facts))
        "failure kernel disagreement lost peer-equality fact"
    other -> Left ("failure kernel disagreement did not fail closed: " <> show other)

rootTerminalAccepts :: Either String ()
rootTerminalAccepts = do
  runtime <- fullyTerminalRuntime
  disposition <- mapLeft show $
    classifyProcessNetworkCertified emptyRootClosure [] runtime
  case certifiedTerminalDispositionNative disposition of
    NetworkTerminal fact -> do
      let state = certifiedTerminalRuntimeState runtime
      assert
        (Map.keysSet (rootTerminalProcesses fact)
          == Map.keysSet (processNetworkPopulation (runtimeNetwork state)))
        "certified root terminal fact did not cover exact static population"
    other -> Left ("all-process Certified closure was not terminal: " <> show other)

rootResidueNativePrecedence :: Either String ()
rootResidueNativePrecedence = do
  runtime <- fullyTerminalRuntime
  let obligation = ObligationId "terminal.production.root"
      openRoot = emptyRootClosure
        { rootOpenObligations = Set.singleton obligation }
  case classifyProcessNetworkCertified openRoot [] runtime of
    Left (ConcurrencyTerminalNativeError (RootTerminalOpenObligations obligations)) ->
      assert (obligations == Set.singleton obligation)
        "root-residue rejection lost exact obligation"
    other -> Left ("root residue did not preserve native diagnostic: " <> show other)

rootKernelDisagreementRejects :: Either String ()
rootKernelDisagreementRejects =
  case verifyRootTerminalKernelFacts
      (RootTerminalKernelFacts True True True True False True) of
    Left (ConcurrencyTerminalRootKernelDisagreement facts) ->
      assert (not (terminalNoInventedFacts facts))
        "root kernel disagreement lost no-invention fact"
    other -> Left ("root kernel disagreement did not fail closed: " <> show other)

stuckAccepts :: Either String ()
stuckAccepts = do
  runtime0 <- baseRuntime
  let state0 = certifiedTerminalRuntimeState runtime0
      (processA, processB) = processKeys (runtimeNetwork state0)
  runtime <- mapLeft show $ applyDeclaredTerminalTransitionCertified
    (terminalTransition processA (Closed doneOutcome)) runtime0
  disposition <- mapLeft show $
    classifyProcessNetworkCertified emptyRootClosure [] runtime
  case certifiedTerminalDispositionNative disposition of
    NetworkStuck active ->
      assert (active == Set.singleton processB)
        "certified stuck disposition lost exact running process"
    other -> Left ("blocked active process was not classified stuck: " <> show other)

enabledLocalCanStep :: Either String ()
enabledLocalCanStep = do
  runtime0 <- baseRuntime
  let state0 = certifiedTerminalRuntimeState runtime0
      (processA, processB) = processKeys (runtimeNetwork state0)
  runtime <- mapLeft show $ applyDeclaredTerminalTransitionCertified
    (terminalTransition processA (Closed doneOutcome)) runtime0
  enabled <- mapLeft show $ certifyEnabledLocalStep runtime processB
  disposition <- mapLeft show $
    classifyProcessNetworkCertified emptyRootClosure [enabled] runtime
  assert
    (certifiedTerminalDispositionNative disposition == NetworkCanStep)
    "certified enabled local step did not produce can-step disposition"

terminalEnabledRejects :: Either String ()
terminalEnabledRejects = do
  runtime0 <- baseRuntime
  let state0 = certifiedTerminalRuntimeState runtime0
      (processA, _) = processKeys (runtimeNetwork state0)
  runtime <- mapLeft show $ applyDeclaredTerminalTransitionCertified
    (terminalTransition processA (Closed doneOutcome)) runtime0
  case certifyEnabledLocalStep runtime processA of
    Left (ConcurrencyTerminalEnabledLocalStepInvalid actual) ->
      assert (actual == processA) "enabled-step rejection lost exact ProcessKey"
    other -> Left ("terminal process was certified as locally enabled: " <> show other)

stuckKernelDisagreementRejects :: Either String ()
stuckKernelDisagreementRejects =
  case verifyNetworkStuckKernelFacts
      (NetworkStuckKernelFacts True True False) of
    Left (ConcurrencyTerminalStuckKernelDisagreement facts) ->
      assert (not (stuckNoEnabledSemanticStep facts))
        "stuck kernel disagreement lost enabledness fact"
    other -> Left ("stuck kernel disagreement did not fail closed: " <> show other)

fullyTerminalRuntime :: Either String CertifiedTerminalRuntime
fullyTerminalRuntime = do
  runtime0 <- baseRuntime
  let state0 = certifiedTerminalRuntimeState runtime0
      (processA, processB) = processKeys (runtimeNetwork state0)
  runtimeA <- mapLeft show $ applyDeclaredTerminalTransitionCertified
    (terminalTransition processA (Closed doneOutcome)) runtime0
  mapLeft show $ applyDeclaredTerminalTransitionCertified
    (terminalTransition processB (Closed doneOutcome)) runtimeA

baseRuntime :: Either String CertifiedTerminalRuntime
baseRuntime = do
  graph <- mapLeft show rootGraph
  network0 <- mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]
  let (processA, processB) = processKeys network0
      contracts =
        [ ProcessActivationContract processA []
        , ProcessActivationContract processB []
        ]
  activation <- mapLeft show $
    certifyRendezvousActivation graph network0 contracts [] []
  mapLeft show $ initializeCertifiedTerminalRuntime
    activation
    (Map.fromList
      [ (processA, emptyProtocolContext)
      , (processB, emptyProtocolContext)
      ])
    Map.empty

terminalTransition :: ProcessKey -> Control -> DeclaredTerminalTransition
terminalTransition processKey control = DeclaredTerminalTransition
  { declaredTerminalProcess = processKey
  , declaredTerminalControl = control
  , declaredTerminalDisposals = []
  }

emptyRootClosure :: RootClosureState
emptyRootClosure = RootClosureState
  { rootOpenResources = Set.empty
  , rootOpenObligations = Set.empty
  , rootPendingObservables = Set.empty
  }

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

doneOutcome :: Outcome
doneOutcome = Outcome "done"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
