{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types (Digest (..), RevisionId (..))
import Phil.Core.Process (ProcessKey (..))
import Phil.Systems.IR (StageContract (..))
import Phil.Systems.ProcessRealization
import Phil.Systems.RuntimeCarrierCoverage
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DEP-002 carrier survives process-local execution-domain transfer" preservedCarrierAccepts
    , test "DEP-002 carrier may be replaced across execution-domain transfer" replacementCarrierAccepts
    , test "DEP-002 discharged carrier does not persist past exact boundary" dischargedCarrierAccepts
    , test "DEP-002 ended carrier validity does not persist past exact boundary" endedValidityAccepts
    , test "DEP-002 uncovered accelerator use rejects" uncoveredAcceleratorRejects
    , test "DEP-002 shared worker cannot leak carrier to another ProcessKey" sharedWorkerDoesNotTransferCarrier
    , test "DEP-002 overflow failure attribution remains ProcessKey-local" failureAttributionStaysLocal
    , test "DEP-002 RuntimeBound closure remains profile-gated" forbiddenProfileRejects
    , test "DEP-002 carrier cannot invent a StageContract obligation" unknownStageObligationRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

preservedCarrierAccepts :: Either String ()
preservedCarrierAccepts =
  mapLeft show $ checkRuntimeCarrierCoverage
    checkedRuntimeProfile stageContract realization
    (Map.singleton carrierAllKey carrierAll)
    usesWithSingleCarrier [preserveTransition]

replacementCarrierAccepts :: Either String ()
replacementCarrierAccepts =
  mapLeft show $ checkRuntimeCarrierCoverage
    checkedRuntimeProfile stageContract realization
    (Map.fromList
      [ (carrierCpuKey, carrierCpu)
      , (carrierAcceleratorKey, carrierAccelerator)
      ])
    usesWithReplacement [replaceTransition]

dischargedCarrierAccepts :: Either String ()
dischargedCarrierAccepts =
  mapLeft show $ checkRuntimeCarrierCoverage
    checkedRuntimeProfile stageContract realization
    (Map.singleton carrierCpuKey carrierCpu)
    usesAfterClosure [dischargeTransition]

endedValidityAccepts :: Either String ()
endedValidityAccepts =
  mapLeft show $ checkRuntimeCarrierCoverage
    checkedRuntimeProfile stageContract realization
    (Map.singleton carrierCpuKey carrierCpu)
    usesAfterClosure [endValidityTransition]

uncoveredAcceleratorRejects :: Either String ()
uncoveredAcceleratorRejects =
  let incompleteCarrier = carrierAll
        { runtimeCarrierExecutions = Set.singleton sharedWorker }
  in case checkRuntimeCarrierCoverage
      checkedRuntimeProfile stageContract realization
      (Map.singleton carrierAllKey incompleteCarrier)
      usesWithSingleCarrier [preserveTransition] of
    Left (RuntimeCarrierUseExecutionUncovered useId key execution) ->
      assert
        ( useId == "use.a.accelerator"
          && key == carrierAllKey
          && execution == acceleratorStage
        )
        "uncovered-use rejection lost exact use/carrier/execution identity"
    other -> Left ("uncovered accelerator use was accepted: " <> show other)

sharedWorkerDoesNotTransferCarrier :: Either String ()
sharedWorkerDoesNotTransferCarrier =
  let foreignUse = RuntimeCarrierUse
        { runtimeCarrierUseId = "use.b.shared-worker"
        , runtimeCarrierUseObligation = overflowObligation
        , runtimeCarrierUseProcess = processB
        , runtimeCarrierUseExecution = sharedWorker
        , runtimeCarrierUseFailureFactId = Just failureFactAId
        , runtimeCarrierUseDisposition = RuntimeUseCovered carrierAllKey
        }
      uses = [useAShared, useAAccelerator, foreignUse]
  in case checkRuntimeCarrierCoverage
      checkedRuntimeProfile stageContract realization
      (Map.singleton carrierAllKey carrierAll)
      uses [preserveTransition] of
    Left (RuntimeCarrierUseProcessMismatch useId expected actual) ->
      assert
        (useId == "use.b.shared-worker" && expected == processA && actual == processB)
        "cross-process rejection lost exact use/process identities"
    other -> Left ("shared physical worker leaked carrier between ProcessKeys: " <> show other)

failureAttributionStaysLocal :: Either String ()
failureAttributionStaysLocal =
  let wrongFailureCarrier = carrierAll
        { runtimeCarrierFailureFactId = failureFactBId }
  in case checkRuntimeCarrierCoverage
      checkedRuntimeProfile stageContract realization
      (Map.singleton carrierAllKey wrongFailureCarrier)
      usesWithSingleCarrier [preserveTransition] of
    Left (RuntimeCarrierFailureFactProcessMismatch key factId expected actual) ->
      assert
        ( key == carrierAllKey
          && factId == failureFactBId
          && expected == processA
          && actual == processB
        )
        "failure-attribution rejection lost exact carrier/fact/process identity"
    other -> Left ("worker/domain mapping retargeted overflow failure attribution: " <> show other)

forbiddenProfileRejects :: Either String ()
forbiddenProfileRejects =
  case checkRuntimeCarrierCoverage
      certifiedReleaseProfile stageContract realization
      (Map.singleton carrierAllKey carrierAll)
      usesWithSingleCarrier [preserveTransition] of
    Left (RuntimeCarrierRuntimeBoundForbidden revision) ->
      assert (revision == "profile.certified-release.no-runtime-bound.v1")
        "profile rejection lost exact assurance-profile revision"
    other -> Left ("profile silently admitted RuntimeBound carrier: " <> show other)

unknownStageObligationRejects :: Either String ()
unknownStageObligationRejects =
  let contract = stageContract { stageDerivedObligations = [] }
  in case checkRuntimeCarrierCoverage
      checkedRuntimeProfile contract realization
      (Map.singleton carrierAllKey carrierAll)
      usesWithSingleCarrier [preserveTransition] of
    Left (RuntimeCarrierObligationNotDerived key obligation) ->
      assert (key == carrierAllKey && obligation == overflowObligation)
        "unknown-obligation rejection lost exact carrier/obligation identity"
    other -> Left ("carrier invented an obligation absent from StageContract: " <> show other)

checkedRuntimeProfile, certifiedReleaseProfile :: RuntimeCarrierProfile
checkedRuntimeProfile = RuntimeCarrierProfile
  { runtimeCarrierProfileRevision = "profile.checked-runtime.v1"
  , runtimeCarrierProfilePermitsRuntimeBound = True
  }
certifiedReleaseProfile = RuntimeCarrierProfile
  { runtimeCarrierProfileRevision = "profile.certified-release.no-runtime-bound.v1"
  , runtimeCarrierProfilePermitsRuntimeBound = False
  }

carrierAllKey, carrierCpuKey, carrierAcceleratorKey :: RuntimeCarrierKey
carrierAllKey = RuntimeCarrierKey "carrier.a.checked-overflow"
carrierCpuKey = RuntimeCarrierKey "carrier.a.checked-overflow.cpu"
carrierAcceleratorKey = RuntimeCarrierKey "carrier.a.checked-overflow.accelerator"

carrierAll, carrierCpu, carrierAccelerator :: RuntimeCarrier
carrierAll = RuntimeCarrier
  { runtimeCarrierKey = carrierAllKey
  , runtimeCarrierObligation = overflowObligation
  , runtimeCarrierProcess = processA
  , runtimeCarrierExecutions = Set.fromList [sharedWorker, acceleratorStage]
  , runtimeCarrierFailureFactId = failureFactAId
  }
carrierCpu = carrierAll
  { runtimeCarrierKey = carrierCpuKey
  , runtimeCarrierExecutions = Set.singleton sharedWorker
  }
carrierAccelerator = carrierAll
  { runtimeCarrierKey = carrierAcceleratorKey
  , runtimeCarrierExecutions = Set.singleton acceleratorStage
  }

usesWithSingleCarrier, usesWithReplacement, usesAfterClosure :: [RuntimeCarrierUse]
usesWithSingleCarrier = [useAShared, useAAccelerator, useBStaticallySafe]
usesWithReplacement =
  [ useAShared { runtimeCarrierUseDisposition = RuntimeUseCovered carrierCpuKey }
  , useAAccelerator { runtimeCarrierUseDisposition = RuntimeUseCovered carrierAcceleratorKey }
  , useBStaticallySafe
  ]
usesAfterClosure =
  [ useAShared { runtimeCarrierUseDisposition = RuntimeUseCovered carrierCpuKey }
  , useAAccelerator
      { runtimeCarrierUseFailureFactId = Nothing
      , runtimeCarrierUseDisposition = RuntimeUseStaticallySafe
      }
  , useBStaticallySafe
  ]

useAShared, useAAccelerator, useBStaticallySafe :: RuntimeCarrierUse
useAShared = RuntimeCarrierUse
  { runtimeCarrierUseId = "use.a.shared-worker"
  , runtimeCarrierUseObligation = overflowObligation
  , runtimeCarrierUseProcess = processA
  , runtimeCarrierUseExecution = sharedWorker
  , runtimeCarrierUseFailureFactId = Just failureFactAId
  , runtimeCarrierUseDisposition = RuntimeUseCovered carrierAllKey
  }
useAAccelerator = RuntimeCarrierUse
  { runtimeCarrierUseId = "use.a.accelerator"
  , runtimeCarrierUseObligation = overflowObligation
  , runtimeCarrierUseProcess = processA
  , runtimeCarrierUseExecution = acceleratorStage
  , runtimeCarrierUseFailureFactId = Just failureFactAId
  , runtimeCarrierUseDisposition = RuntimeUseCovered carrierAllKey
  }
useBStaticallySafe = RuntimeCarrierUse
  { runtimeCarrierUseId = "use.b.shared-worker.safe"
  , runtimeCarrierUseObligation = overflowObligation
  , runtimeCarrierUseProcess = processB
  , runtimeCarrierUseExecution = sharedWorker
  , runtimeCarrierUseFailureFactId = Nothing
  , runtimeCarrierUseDisposition = RuntimeUseStaticallySafe
  }

preserveTransition, replaceTransition, dischargeTransition, endValidityTransition :: RuntimeCarrierTransition
preserveTransition = baseTransition (CarrierPreserved carrierAllKey)
replaceTransition = baseTransition (CarrierReplaced carrierCpuKey carrierAcceleratorKey)
dischargeTransition = baseTransition
  (CarrierDischarged carrierCpuKey "range proof discharged before accelerator use")
endValidityTransition = baseTransition
  (CarrierValidityEnded carrierCpuKey "checked operation validity ended at domain boundary")

baseTransition :: RuntimeCarrierTransitionDisposition -> RuntimeCarrierTransition
baseTransition disposition = RuntimeCarrierTransition
  { runtimeCarrierTransitionId = "transfer.a.cpu-to-accelerator"
  , runtimeCarrierTransitionObligation = overflowObligation
  , runtimeCarrierTransitionProcess = processA
  , runtimeCarrierTransitionFrom = sharedWorker
  , runtimeCarrierTransitionTo = acceleratorStage
  , runtimeCarrierTransitionDisposition = disposition
  }

overflowObligation :: RevisionId
overflowObligation = RevisionId "obligation.uint.checked-overflow.a.v1"

failureFactAId, failureFactBId :: Text
failureFactAId = "process.failure.a.checked-overflow"
failureFactBId = "process.failure.b.checked-overflow"

processA, processB :: ProcessKey
processA = ProcessKey "process.a"
processB = ProcessKey "process.b"

sharedWorker, acceleratorStage :: PhysicalExecutionKey
sharedWorker = PhysicalExecutionKey "event-loop.worker-0"
acceleratorStage = PhysicalExecutionKey "accelerator.stage-7"

realization :: ProcessExecutionRealization
realization = ProcessExecutionRealization
  { realizationProcessExecutions = Map.fromList
      [ (processA, Set.fromList [sharedWorker, acceleratorStage])
      , (processB, Set.singleton sharedWorker)
      ]
  , realizationEventExecutions = Map.empty
  , realizationPhysicalCausality = Set.empty
  , realizationRestrictedOwners = Map.empty
  , realizationSemanticFacts = Set.fromList
      [ ProcessSemanticFact failureFactAId processA ProcessFailureFact "uint.checked.overflow"
      , ProcessSemanticFact failureFactBId processB ProcessFailureFact "uint.checked.overflow"
      ]
  , realizationTerminalFacts = Map.empty
  , realizationExecutionDecisions = Map.empty
  , realizationAssumptions = Set.empty
  }

stageContract :: StageContract
stageContract = StageContract
  { stageContractId = "stage.dep002.runtime-carrier"
  , stageSourceArtifactDigest = Digest "source.dep002"
  , stageTargetArtifactDigest = Digest "target.dep002"
  , stageFacts = []
  , stageInvariants = Map.empty
  , stageRequiredEdges = []
  , stageDerivedObligations = [overflowObligation]
  , stageAssumptions = []
  , stageTraceRelation = []
  , stageResourceFailureRelation = []
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
