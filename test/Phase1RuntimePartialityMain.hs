{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.Types (RevisionId (..))
import Phil.Examples.Phase1.TargetStrengtheningWitnesses
  ( steveHostAbiStrengtheningRef
  , steveTargetStrengtheningStage
  )
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveHostAbiObligationRevision
  )
import Phil.Systems.IR (DecisionId (..))
import Phil.Systems.RuntimePartialityRelation
import Phil.Systems.TargetStrengthening
  ( TargetPreconditionRef (..)
  , TargetStrengthening (..)
  , TargetStrengtheningStageBundle (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-012 explicit deployment requirement covers UB/poison/unreachable/trap"
        explicitDeploymentDispositionAccepts
    , test "EXEC-012 exact admitted source outcome may absorb target partiality"
        mappedSourceOutcomeAccepts
    , test "EXEC-012 retained obligation may be runtime-enforced explicitly"
        runtimeEnforcementAccepts
    , test "EXEC-012 ambient target convention is not proof of a precondition"
        unboundProofRevisionRejects
    , test "EXEC-012 every classified hazard requires an exact disposition"
        missingHazardDispositionRejects
    , test "EXEC-012 hazard-kind substitution cannot satisfy another hazard"
        hazardKindSubstitutionRejects
    , test "EXEC-012 undeclared source outcome cannot absorb target partiality"
        undeclaredSourceOutcomeRejects
    , test "EXEC-012 unknown target precondition cannot enter the relation"
        unknownTargetPreconditionRejects
    , test "EXEC-012 empty deployment identity cannot close partiality"
        emptyDeploymentRequirementRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

explicitDeploymentDispositionAccepts :: Either String ()
explicitDeploymentDispositionAccepts = do
  base <- steveStage
  let relation = baseRelation base
        (Map.fromList
          [ (hazard TargetUndefinedBehavior, deployment)
          , (hazard TargetPoison, deployment)
          , (hazard TargetUnreachable, deployment)
          , (hazard TargetTrap, deployment)
          ])
  _ <- mapLeft show (checkRuntimePartialityRelation relation)
  Right ()
  where
    deployment = RuntimePartialityDeploymentRequirement
      (RuntimePartialityDeploymentRequirementKey "deploy.steve.host-abi.v1")

mappedSourceOutcomeAccepts :: Either String ()
mappedSourceOutcomeAccepts = do
  base <- steveStage
  let outcome = RuntimePartialitySourceOutcome "host-abi-precondition-failure"
      relation = (baseRelation base
          (Map.fromList
            [ (hazard TargetUndefinedBehavior,
                RuntimePartialityMapsToSourceOutcome outcome)
            , (hazard TargetPoison,
                RuntimePartialityMapsToSourceOutcome outcome)
            , (hazard TargetUnreachable,
                RuntimePartialityMapsToSourceOutcome outcome)
            , (hazard TargetTrap,
                RuntimePartialityMapsToSourceOutcome outcome)
            ]))
        { runtimePartialitySourceOutcomes = Set.singleton outcome }
  _ <- mapLeft show (checkRuntimePartialityRelation relation)
  Right ()

runtimeEnforcementAccepts :: Either String ()
runtimeEnforcementAccepts = do
  base <- steveStage
  let enforcement = RuntimePartialityRuntimeEnforced
        (RuntimePartialityEnforcementKey "runtime.guard.host-abi")
      relation = baseRelation base
        (Map.fromList
          [ (hazard TargetUndefinedBehavior, enforcement)
          , (hazard TargetPoison, enforcement)
          , (hazard TargetUnreachable, enforcement)
          , (hazard TargetTrap, enforcement)
          ])
  _ <- mapLeft show (checkRuntimePartialityRelation relation)
  Right ()

unboundProofRevisionRejects :: Either String ()
unboundProofRevisionRejects = do
  base <- steveStage
  let fake = RevisionId "native-abi-folklore"
      relation = baseRelation base
        (Map.fromList
          [ (hazard TargetUndefinedBehavior,
              RuntimePartialityProvedSatisfied fake)
          , (hazard TargetPoison, deployment)
          , (hazard TargetUnreachable, deployment)
          , (hazard TargetTrap, deployment)
          ])
  case checkRuntimePartialityRelation relation of
    Left (RuntimePartialityUnknownAssuranceRevision actual revision) -> do
      assert (actual == hazard TargetUndefinedBehavior)
        "wrong hazard reported for unbound proof revision"
      assert (revision == fake)
        "unbound proof rejection lost exact revision identity"
    other -> Left ("ambient target convention was accepted as proof: " <> show other)
  where
    deployment = RuntimePartialityDeploymentRequirement
      (RuntimePartialityDeploymentRequirementKey "deploy.steve.host-abi.v1")

missingHazardDispositionRejects :: Either String ()
missingHazardDispositionRejects = do
  base <- steveStage
  let deployment = RuntimePartialityDeploymentRequirement
        (RuntimePartialityDeploymentRequirementKey "deploy.steve.host-abi.v1")
      actual = Map.fromList
        [ (hazard TargetUndefinedBehavior, deployment)
        , (hazard TargetPoison, deployment)
        , (hazard TargetUnreachable, deployment)
        ]
      relation = baseRelation base actual
      expected = Set.fromList
        [ hazard TargetUndefinedBehavior
        , hazard TargetPoison
        , hazard TargetUnreachable
        , hazard TargetTrap
        ]
  case checkRuntimePartialityRelation relation of
    Left (RuntimePartialityDispositionDomainMismatch expectedActual actualDomain) -> do
      assert (expectedActual == expected)
        "missing-disposition rejection changed expected hazard domain"
      assert (actualDomain == Map.keysSet actual)
        "missing-disposition rejection changed actual hazard domain"
    other -> Left ("target trap disappeared without a disposition: " <> show other)

hazardKindSubstitutionRejects :: Either String ()
hazardKindSubstitutionRejects = do
  base <- steveStage
  let deployment = RuntimePartialityDeploymentRequirement
        (RuntimePartialityDeploymentRequirementKey "deploy.steve.host-abi.v1")
      substituted = RuntimePartialityHazardRef
        steveHostAbiStrengtheningRef TargetExceptionalHalt
      actual = Map.fromList
        [ (hazard TargetUndefinedBehavior, deployment)
        , (hazard TargetPoison, deployment)
        , (hazard TargetUnreachable, deployment)
        , (substituted, deployment)
        ]
      relation = baseRelation base actual
  case checkRuntimePartialityRelation relation of
    Left (RuntimePartialityDispositionDomainMismatch _ _) -> Right ()
    other -> Left ("exceptional-halt identity substituted for target trap: " <> show other)

undeclaredSourceOutcomeRejects :: Either String ()
undeclaredSourceOutcomeRejects = do
  base <- steveStage
  let outcome = RuntimePartialitySourceOutcome "invented-target-failure"
      deployment = RuntimePartialityDeploymentRequirement
        (RuntimePartialityDeploymentRequirementKey "deploy.steve.host-abi.v1")
      relation = baseRelation base
        (Map.fromList
          [ (hazard TargetUndefinedBehavior,
              RuntimePartialityMapsToSourceOutcome outcome)
          , (hazard TargetPoison, deployment)
          , (hazard TargetUnreachable, deployment)
          , (hazard TargetTrap, deployment)
          ])
  case checkRuntimePartialityRelation relation of
    Left (RuntimePartialityUndeclaredSourceOutcome actual actualOutcome) -> do
      assert (actual == hazard TargetUndefinedBehavior)
        "undeclared source-outcome rejection changed hazard identity"
      assert (actualOutcome == outcome)
        "undeclared source-outcome rejection changed outcome identity"
    other -> Left ("target UB invented a new source failure: " <> show other)

unknownTargetPreconditionRejects :: Either String ()
unknownTargetPreconditionRejects = do
  base <- steveStage
  let unknown = TargetPreconditionRef
        { targetPreconditionDecision = DecisionId "unknown.lowering"
        , targetPreconditionRequirement = "pointer must be aligned"
        }
      relation = RuntimePartialityRelation
        { runtimePartialityTargetStage = base
        , runtimePartialityHazards = Map.singleton unknown
            (Set.singleton TargetUndefinedBehavior)
        , runtimePartialitySourceOutcomes = Set.empty
        , runtimePartialityDispositions = Map.singleton
            (RuntimePartialityHazardRef unknown TargetUndefinedBehavior)
            (RuntimePartialityDeploymentRequirement
              (RuntimePartialityDeploymentRequirementKey "deploy.unknown"))
        }
  case checkRuntimePartialityRelation relation of
    Left (RuntimePartialityUnknownTargetPreconditions actual) ->
      assert (actual == Set.singleton unknown)
        "unknown-target-precondition rejection lost exact precondition identity"
    other -> Left ("unintroduced target precondition entered partiality relation: " <> show other)

emptyDeploymentRequirementRejects :: Either String ()
emptyDeploymentRequirementRejects = do
  base <- steveStage
  let deployment = RuntimePartialityDeploymentRequirement
        (RuntimePartialityDeploymentRequirementKey "deploy.steve.host-abi.v1")
      relation = baseRelation base
        (Map.fromList
          [ (hazard TargetUndefinedBehavior,
              RuntimePartialityDeploymentRequirement
                (RuntimePartialityDeploymentRequirementKey ""))
          , (hazard TargetPoison, deployment)
          , (hazard TargetUnreachable, deployment)
          , (hazard TargetTrap, deployment)
          ])
  case checkRuntimePartialityRelation relation of
    Left (RuntimePartialityEmptyDeploymentRequirementKey actual) ->
      assert (actual == hazard TargetUndefinedBehavior)
        "empty deployment requirement rejection changed hazard identity"
    other -> Left ("empty deployment identity closed target UB: " <> show other)

baseRelation
  :: TargetStrengtheningStageBundle
  -> Map.Map RuntimePartialityHazardRef RuntimePartialityDisposition
  -> RuntimePartialityRelation
baseRelation base dispositions = RuntimePartialityRelation
  { runtimePartialityTargetStage = base
  , runtimePartialityHazards = Map.singleton steveHostAbiStrengtheningRef
      (Set.fromList
        [ TargetUndefinedBehavior
        , TargetPoison
        , TargetUnreachable
        , TargetTrap
        ])
  , runtimePartialitySourceOutcomes = Set.empty
  , runtimePartialityDispositions = dispositions
  }

hazard :: TargetPartialityKind -> RuntimePartialityHazardRef
hazard = RuntimePartialityHazardRef steveHostAbiStrengtheningRef

steveStage :: Either String TargetStrengtheningStageBundle
steveStage = do
  stage <- steveTargetStrengtheningStage
  let retained = Map.lookup steveHostAbiStrengtheningRef
        (targetStrengtheningStageFacts stage)
        >>= targetStrengtheningDerivedObligation
  assert (retained == Just steveHostAbiObligationRevision)
    "Steve target-strengthening witness lost the host-ABI derived obligation"
  Right stage

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
