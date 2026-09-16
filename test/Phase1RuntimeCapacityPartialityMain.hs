{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.TargetStrengtheningWitnesses
  ( steveHostAbiStrengtheningRef
  , steveTargetStrengtheningStage
  )
import Phil.Systems.RuntimePartialityRelation
import Phil.Systems.TargetStrengthening
  ( TargetStrengtheningStageBundle
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-013 canonical capacity classes remain distinct and explicitly dispositioned"
        canonicalCapacityClassesAccept
    , test "EXEC-013 missing capacity disposition rejects realization"
        missingCapacityDispositionRejects
    , test "EXEC-013 capacity-class substitution cannot discharge another limit"
        capacityClassSubstitutionRejects
    , test "EXEC-013 capacity may map to an exact admitted source outcome"
        capacityMapsToSourceOutcome
    , test "EXEC-013 capacity may retain exact obligation under runtime enforcement"
        capacityRuntimeEnforcementAccepts
    , test "EXEC-013 capacity may depend on an explicit assumption"
        capacityAssumptionAccepts
    , test "EXEC-013 capacity may become an explicit deployment requirement"
        capacityDeploymentRequirementAccepts
    , test "EXEC-013 empty extensible capacity identity rejects"
        emptyOtherCapacityRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

canonicalCapacityClassesAccept :: Either String ()
canonicalCapacityClassesAccept = do
  stage <- steveTargetStrengtheningStage
  assert (Set.size (Set.fromList capacityClasses) == length capacityClasses)
    "capacity taxonomy collapsed distinct semantic classes"
  let dispositions = Map.fromList
        [ (capacityHazard capacity, deployment)
        | capacity <- capacityClasses
        ]
      relation = relationFor stage (Set.fromList capacityClasses) dispositions
  _ <- mapLeft show (checkRuntimePartialityRelation relation)
  Right ()

missingCapacityDispositionRejects :: Either String ()
missingCapacityDispositionRejects = do
  stage <- steveTargetStrengtheningStage
  let classes = Set.fromList capacityClasses
      missing = TargetWorkerTaskCapacity
      dispositions = Map.fromList
        [ (capacityHazard capacity, deployment)
        | capacity <- capacityClasses
        , capacity /= missing
        ]
      relation = relationFor stage classes dispositions
  case checkRuntimePartialityRelation relation of
    Left (RuntimePartialityDispositionDomainMismatch expected actual) -> do
      assert (Set.member (capacityHazard missing) expected)
        "missing worker/task capacity vanished from expected hazard domain"
      assert (not (Set.member (capacityHazard missing) actual))
        "missing worker/task capacity appeared in actual disposition domain"
    other -> Left ("missing capacity disposition was accepted: " <> show other)

capacityClassSubstitutionRejects :: Either String ()
capacityClassSubstitutionRejects = do
  stage <- steveTargetStrengtheningStage
  let expectedClass = TargetGasOrFuelCapacity
      substitutedClass = TargetDescriptorTableQueueCapacity
      relation = relationFor stage
        (Set.singleton expectedClass)
        (Map.singleton (capacityHazard substitutedClass) deployment)
  case checkRuntimePartialityRelation relation of
    Left RuntimePartialityDispositionDomainMismatch {} -> Right ()
    other -> Left ("capacity class substitution was accepted: " <> show other)

capacityMapsToSourceOutcome :: Either String ()
capacityMapsToSourceOutcome = do
  stage <- steveTargetStrengtheningStage
  let outcome = RuntimePartialitySourceOutcome "source.capacity-exhausted"
      capacity = TargetGasOrFuelCapacity
      relation = (relationFor stage
          (Set.singleton capacity)
          (Map.singleton (capacityHazard capacity)
            (RuntimePartialityMapsToSourceOutcome outcome)))
        { runtimePartialitySourceOutcomes = Set.singleton outcome }
  _ <- mapLeft show (checkRuntimePartialityRelation relation)
  Right ()

capacityRuntimeEnforcementAccepts :: Either String ()
capacityRuntimeEnforcementAccepts = do
  stage <- steveTargetStrengtheningStage
  let capacity = TargetDescriptorTableQueueCapacity
      disposition = RuntimePartialityRuntimeEnforced
        (RuntimePartialityEnforcementKey "runtime.capacity.queue-bound.v1")
      relation = relationFor stage
        (Set.singleton capacity)
        (Map.singleton (capacityHazard capacity) disposition)
  _ <- mapLeft show (checkRuntimePartialityRelation relation)
  Right ()

capacityAssumptionAccepts :: Either String ()
capacityAssumptionAccepts = do
  stage <- steveTargetStrengtheningStage
  let capacity = TargetPinnedOrDmaCapacity
      disposition = RuntimePartialityAssumption
        (RuntimePartialityAssumptionKey "assume.pinned-dma-capacity.v1")
      relation = relationFor stage
        (Set.singleton capacity)
        (Map.singleton (capacityHazard capacity) disposition)
  _ <- mapLeft show (checkRuntimePartialityRelation relation)
  Right ()

capacityDeploymentRequirementAccepts :: Either String ()
capacityDeploymentRequirementAccepts = do
  stage <- steveTargetStrengtheningStage
  let capacity = TargetDeviceLocalMemoryCapacity
      relation = relationFor stage
        (Set.singleton capacity)
        (Map.singleton (capacityHazard capacity) deployment)
  _ <- mapLeft show (checkRuntimePartialityRelation relation)
  Right ()

emptyOtherCapacityRejects :: Either String ()
emptyOtherCapacityRejects = do
  stage <- steveTargetStrengtheningStage
  let capacity = TargetOtherCapacity "   "
      hazard = capacityHazard capacity
      relation = relationFor stage
        (Set.singleton capacity)
        (Map.singleton hazard deployment)
  case checkRuntimePartialityRelation relation of
    Left (RuntimePartialityEmptyHazardIdentity actual) ->
      assert (actual == hazard)
        "empty custom-capacity rejection changed hazard identity"
    other -> Left ("empty custom capacity identity was accepted: " <> show other)

capacityClasses :: [TargetCapacityClass]
capacityClasses =
  [ TargetStackOrDepthCapacity
  , TargetGasOrFuelCapacity
  , TargetDescriptorTableQueueCapacity
  , TargetWorkerTaskCapacity
  , TargetDeviceLaunchCapacity
  , TargetDeviceScratchCapacity
  , TargetDeviceRegisterCapacity
  , TargetDeviceLocalMemoryCapacity
  , TargetPinnedOrDmaCapacity
  , TargetAllocatorCapacity
  , TargetOtherCapacity "accelerator.shared-memory"
  ]

capacityHazard :: TargetCapacityClass -> RuntimePartialityHazardRef
capacityHazard capacity = RuntimePartialityHazardRef
  steveHostAbiStrengtheningRef
  (TargetCapacityExhaustion capacity)

relationFor
  :: TargetStrengtheningStageBundle
  -> Set.Set TargetCapacityClass
  -> Map.Map RuntimePartialityHazardRef RuntimePartialityDisposition
  -> RuntimePartialityRelation
relationFor stage capacities dispositions = RuntimePartialityRelation
  { runtimePartialityTargetStage = stage
  , runtimePartialityHazards = Map.singleton steveHostAbiStrengtheningRef
      (Set.map TargetCapacityExhaustion capacities)
  , runtimePartialitySourceOutcomes = Set.empty
  , runtimePartialityDispositions = dispositions
  }

deployment :: RuntimePartialityDisposition
deployment = RuntimePartialityDeploymentRequirement
  (RuntimePartialityDeploymentRequirementKey "deploy.capacity-budget.v1")

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform = either (Left . transform) Right
