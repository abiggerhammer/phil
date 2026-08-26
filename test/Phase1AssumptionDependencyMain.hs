{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.AssumptionDependencyWitnesses
import Phil.Examples.Phase1.EvidenceErasureWitnesses
  ( steveErasureAfterDischarge
  , uploadErasureAfterDischarge
  )
import Phil.Systems.AssumptionDependency
import Phil.Systems.EvidenceErasure
  ( verifyEvidenceErasureStageBundle
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-013 SYS-012 upload predecessor remains valid" uploadErasureRegression
    , test "SYS-013 SYS-012 Steve predecessor remains valid" steveErasureRegression
    , test "SYS-013 upload with no inherited assumptions is accepted" uploadNoAssumptionsAccepted
    , test "SYS-013 Steve complete bidirectional assumption lineage is accepted" steveCompleteAccepted
    , test "SYS-013 fact disposition cannot launder an assumption" factAssumptionOmissionRejected
    , test "SYS-013 mechanism justification cannot launder an assumption" mechanismAssumptionOmissionRejected
    , test "SYS-013 erasure cannot launder source-fact assumptions" erasureAssumptionOmissionRejected
    , test "SYS-013 consumer must retain exact validity scope" scopeMismatchRejected
    , test "SYS-013 reverse dependency cannot omit a consumer" reverseOmissionRejected
    , test "SYS-013 registry cannot omit an inherited assumption" registryOmissionRejected
    , test "SYS-013 registry cannot invent an assumption" inventedAssumptionRejected
    , test "SYS-013 assumption validity scope cannot be empty" emptyValidityScopeRejected
    , test "SYS-013 dependency-stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadErasureRegression :: Either String ()
uploadErasureRegression = mapLeft show
  (verifyEvidenceErasureStageBundle uploadErasureAfterDischarge)

steveErasureRegression :: Either String ()
steveErasureRegression = do
  bundle <- steveErasureAfterDischarge
  mapLeft show (verifyEvidenceErasureStageBundle bundle)

uploadNoAssumptionsAccepted :: Either String ()
uploadNoAssumptionsAccepted = mapLeft show
  (verifyAssumptionDependencyStageBundle uploadAssumptionDependencyStage)

steveCompleteAccepted :: Either String ()
steveCompleteAccepted = do
  bundle <- steveAssumptionDependencyStage
  mapLeft show (verifyAssumptionDependencyStageBundle bundle)

factAssumptionOmissionRejected :: Either String ()
factAssumptionOmissionRejected = do
  original <- steveAssumptionDependencyStage
  consumer <- pickFactConsumer original
  assertForwardOmissionRejected original consumer

mechanismAssumptionOmissionRejected :: Either String ()
mechanismAssumptionOmissionRejected = do
  original <- steveAssumptionDependencyStage
  consumer <- pickMechanismConsumer original
  assertForwardOmissionRejected original consumer

erasureAssumptionOmissionRejected :: Either String ()
erasureAssumptionOmissionRejected = do
  original <- steveAssumptionDependencyStage
  consumer <- pickErasureConsumer original
  assertForwardOmissionRejected original consumer

assertForwardOmissionRejected
  :: AssumptionDependencyStageBundle
  -> AssumptionConsumer
  -> Either String ()
assertForwardOmissionRejected original consumer = do
  dependencies <- maybe
    (Left "selected consumer has no forward dependency entry")
    Right
    (Map.lookup consumer (assumptionDependencyStageForward original))
  case Map.minViewWithKey dependencies of
    Nothing -> Left "selected consumer unexpectedly has no assumptions"
    Just ((assumption, _), rest) -> do
      let mutated = rebuild original
            (assumptionDependencyStageAssumptions original)
            (Map.insert consumer rest (assumptionDependencyStageForward original))
            (assumptionDependencyStageReverse original)
      case verifyAssumptionDependencyStageBundle mutated of
        Left (AssumptionForwardSetMismatch actual expected actualSet)
          | actual == consumer
              && Set.member assumption expected
              && not (Set.member assumption actualSet) -> Right ()
        other -> Left ("assumption omission was not rejected correctly: " <> show other)

scopeMismatchRejected :: Either String ()
scopeMismatchRejected = do
  original <- steveAssumptionDependencyStage
  consumer <- pickFactConsumer original
  dependencies <- maybe
    (Left "selected fact consumer has no dependencies")
    Right
    (Map.lookup consumer (assumptionDependencyStageForward original))
  case Map.minViewWithKey dependencies of
    Nothing -> Left "selected fact consumer unexpectedly has no assumptions"
    Just ((assumption, expectedScope), _) -> do
      let wrongScope = AssumptionValidityScopeRevision "scope.wrong.v1"
          badDependencies = Map.insert assumption wrongScope dependencies
          mutated = rebuild original
            (assumptionDependencyStageAssumptions original)
            (Map.insert consumer badDependencies (assumptionDependencyStageForward original))
            (assumptionDependencyStageReverse original)
      case verifyAssumptionDependencyStageBundle mutated of
        Left (AssumptionForwardScopeMismatch actualConsumer actualAssumption expected actual)
          | actualConsumer == consumer
              && actualAssumption == assumption
              && expected == expectedScope
              && actual == wrongScope -> Right ()
        other -> Left ("validity-scope mismatch was accepted: " <> show other)

reverseOmissionRejected :: Either String ()
reverseOmissionRejected = do
  original <- steveAssumptionDependencyStage
  case Map.minViewWithKey (assumptionDependencyStageReverse original) of
    Nothing -> Left "Steve reverse dependency map unexpectedly empty"
    Just ((assumption, consumers), _) ->
      case Set.minView consumers of
        Nothing -> Left "Steve reverse dependency set unexpectedly empty"
        Just (removed, rest) -> do
          let mutated = rebuild original
                (assumptionDependencyStageAssumptions original)
                (assumptionDependencyStageForward original)
                (Map.insert assumption rest (assumptionDependencyStageReverse original))
          case verifyAssumptionDependencyStageBundle mutated of
            Left (AssumptionReverseConsumerMismatch actual expected actualConsumers)
              | actual == assumption
                  && Set.member removed expected
                  && not (Set.member removed actualConsumers) -> Right ()
            other -> Left ("reverse omission was accepted: " <> show other)

registryOmissionRejected :: Either String ()
registryOmissionRejected = do
  original <- steveAssumptionDependencyStage
  case Map.minViewWithKey (assumptionDependencyStageAssumptions original) of
    Nothing -> Left "Steve assumption registry unexpectedly empty"
    Just ((assumption, _), rest) -> do
      let mutated = rebuild original rest
            (assumptionDependencyStageForward original)
            (assumptionDependencyStageReverse original)
      case verifyAssumptionDependencyStageBundle mutated of
        Left (AssumptionRegistryDomainMismatch expected actual)
          | Set.member assumption expected
              && not (Set.member assumption actual) -> Right ()
        other -> Left ("registry omission was accepted: " <> show other)

inventedAssumptionRejected :: Either String ()
inventedAssumptionRejected = do
  original <- steveAssumptionDependencyStage
  let invented = StageAssumptionKey "assumption.invented"
      binding = AssumptionBinding invented
        (AssumptionValidityScopeRevision "scope.assumption.invented.v1")
      registry = Map.insert invented binding
        (assumptionDependencyStageAssumptions original)
      mutated = rebuild original registry
        (assumptionDependencyStageForward original)
        (assumptionDependencyStageReverse original)
  case verifyAssumptionDependencyStageBundle mutated of
    Left (AssumptionRegistryDomainMismatch expected actual)
      | not (Set.member invented expected)
          && Set.member invented actual -> Right ()
    other -> Left ("invented assumption was accepted: " <> show other)

emptyValidityScopeRejected :: Either String ()
emptyValidityScopeRejected = do
  original <- steveAssumptionDependencyStage
  case Map.minViewWithKey (assumptionDependencyStageAssumptions original) of
    Nothing -> Left "Steve assumption registry unexpectedly empty"
    Just ((assumption, binding), _) -> do
      let badBinding = binding
            { assumptionBindingValidityScope = AssumptionValidityScopeRevision "" }
          registry = Map.insert assumption badBinding
            (assumptionDependencyStageAssumptions original)
          mutated = rebuild original registry
            (assumptionDependencyStageForward original)
            (assumptionDependencyStageReverse original)
      case verifyAssumptionDependencyStageBundle mutated of
        Left (AssumptionBindingEmptyValidityScope actual)
          | actual == assumption -> Right ()
        other -> Left ("empty assumption validity scope was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- steveAssumptionDependencyStage
  let reverseMap mapValue = Map.fromList (reverse (Map.toAscList mapValue))
      registry = reverseMap (assumptionDependencyStageAssumptions original)
      forward = Map.fromList
        [ (consumer, reverseMap dependencies)
        | (consumer, dependencies) <- reverse
            (Map.toAscList (assumptionDependencyStageForward original))
        ]
      reverseDependencies = Map.fromList
        [ (assumption, Set.fromList (reverse (Set.toAscList consumers)))
        | (assumption, consumers) <- reverse
            (Map.toAscList (assumptionDependencyStageReverse original))
        ]
      rebuilt = rebuild original registry forward reverseDependencies
  assert
    (assumptionDependencyStageRevision original
      == assumptionDependencyStageRevision rebuilt)
    "assumption dependency revision changed with map/set enumeration order"
  mapLeft show (verifyAssumptionDependencyStageBundle rebuilt)

pickFactConsumer :: AssumptionDependencyStageBundle -> Either String AssumptionConsumer
pickFactConsumer bundle = pick "fact"
  [ consumer
  | consumer@(AssumptionFactConsumer _) <-
      Map.keys (assumptionDependencyStageForward bundle)
  ]

pickMechanismConsumer :: AssumptionDependencyStageBundle -> Either String AssumptionConsumer
pickMechanismConsumer bundle = pick "mechanism"
  [ consumer
  | consumer@(AssumptionMechanismConsumer _) <-
      Map.keys (assumptionDependencyStageForward bundle)
  ]

pickErasureConsumer :: AssumptionDependencyStageBundle -> Either String AssumptionConsumer
pickErasureConsumer bundle = pick "erasure"
  [ consumer
  | consumer@(AssumptionErasureConsumer _) <-
      Map.keys (assumptionDependencyStageForward bundle)
  ]

pick :: String -> [a] -> Either String a
pick label values = case values of
  value : _ -> Right value
  [] -> Left ("no " <> label <> " assumption consumer found")

rebuild
  :: AssumptionDependencyStageBundle
  -> Map.Map StageAssumptionKey AssumptionBinding
  -> Map.Map AssumptionConsumer
      (Map.Map StageAssumptionKey AssumptionValidityScopeRevision)
  -> Map.Map StageAssumptionKey (Set.Set AssumptionConsumer)
  -> AssumptionDependencyStageBundle
rebuild original = makeAssumptionDependencyStageBundle
  (assumptionDependencyStageBase original)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
