{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Authority
import Phil.Core.Callable
  ( CallableContract (..)
  , CalleeTransition (..)
  )
import Phil.Core.CallableRefinement
  ( CallableMachineShape (..)
  , CallableRefinementSurface (..)
  )
import Phil.Core.EnvironmentObservation
import Phil.Core.ProviderQualification
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InterfaceRevision (..)
  )
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-011 ambient environmental observations reject"
        ambientObservationsReject
    , test "EXEC-011 runtime and backend environment mechanisms are not semantic relations"
        runtimeRepresentationsReject
    , test "EXEC-011 exact checked provider observation accepts"
        checkedProviderObservationAccepts
    , test "EXEC-011 provider observation requires an actually qualified operation"
        providerOperationMustBeQualified
    , test "EXEC-011 observation kind cannot be substituted through one explicit relation"
        observationKindMismatchRejects
    , test "EXEC-011 exact checked capability observation accepts"
        checkedCapabilityObservationAccepts
    , test "EXEC-011 explicit entry/protocol/boundary/assumption/deployment relations accept"
        otherExplicitRelationsAccept
    , test "EXEC-011 unknown and duplicate relation identities fail closed"
        relationIdentityIsExact
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

ambientObservationsReject :: Either String ()
ambientObservationsReject =
  mapM_ reject ambientKinds
  where
    reject kind =
      let source = AmbientEnvironmentObservation kind
      in case checkEnvironmentObservation kind source emptyEnvironmentObservationContext of
          Left (EnvironmentObservationSourceNotExplicit actual) ->
            assert (actual == source)
              ("ambient-observation rejection lost exact source: " <> show kind)
          other -> Left
            ("ambient environmental observation was admitted: " <> show kind <> " -> " <> show other)

runtimeRepresentationsReject :: Either String ()
runtimeRepresentationsReject =
  mapM_ reject
    [ RuntimeEnvironmentHandle "clock_gettime"
    , BackendEnvironmentSymbol "llvm.readcyclecounter"
    , AmbientEnvironmentRegistryEntry "process.env"
    ]
  where
    reject source =
      case checkEnvironmentObservation
          EnvironmentClockTime source emptyEnvironmentObservationContext of
        Left (EnvironmentObservationSourceNotExplicit actual) ->
          assert (actual == source) "runtime source identity changed during rejection"
        other -> Left ("runtime/backend mechanism became an environment relation: " <> show other)

checkedProviderObservationAccepts :: Either String ()
checkedProviderObservationAccepts = do
  checkedProvider <- clockProviderQualification
  context <- mapLeft show $
    registerProviderEnvironmentObservation
      clockRelation
      EnvironmentClockTime
      checkedProvider
      clockOperation
      emptyEnvironmentObservationContext
  checked <- mapLeft show $
    checkEnvironmentObservation
      EnvironmentClockTime
      (ExplicitEnvironmentObservation clockRelation)
      context
  assert
    (checkedEnvironmentObservationRelationKey checked == clockRelation)
    "checked provider observation lost relation identity"
  assert
    (checkedEnvironmentObservationKind checked == EnvironmentClockTime)
    "checked provider observation changed observation kind"
  assert
    ( checkedEnvironmentObservationProvenance checked
        == EnvironmentProviderProvenance
            clockProviderRevision clockImplementationRevision clockOperation
    )
    "checked provider observation lost exact provider/operation lineage"

providerOperationMustBeQualified :: Either String ()
providerOperationMustBeQualified = do
  checkedProvider <- clockProviderQualification
  let unqualified = ProviderOperationKey "clock.random"
  case registerProviderEnvironmentObservation
      clockRelation
      EnvironmentRandomness
      checkedProvider
      unqualified
      emptyEnvironmentObservationContext of
    Left (EnvironmentObservationProviderOperationNotQualified actual) ->
      assert (actual == unqualified)
        "unqualified-provider rejection lost operation identity"
    other -> Left
      ("provider supplied an undeclared environmental operation: " <> show other)

observationKindMismatchRejects :: Either String ()
observationKindMismatchRejects = do
  checkedProvider <- clockProviderQualification
  context <- mapLeft show $
    registerProviderEnvironmentObservation
      clockRelation
      EnvironmentClockTime
      checkedProvider
      clockOperation
      emptyEnvironmentObservationContext
  case checkEnvironmentObservation
      EnvironmentRandomness
      (ExplicitEnvironmentObservation clockRelation)
      context of
    Left (EnvironmentObservationKindMismatch requested actual) -> do
      assert (requested == EnvironmentRandomness)
        "kind-mismatch rejection lost requested observation"
      assert (actual == EnvironmentClockTime)
        "kind-mismatch rejection lost admitted observation"
    other -> Left
      ("one explicit environment relation was relabeled as another observation: " <> show other)

checkedCapabilityObservationAccepts :: Either String ()
checkedCapabilityObservationAccepts = do
  state <- mapLeft show $
    insertAuthorityCapability randomCapability emptyAuthorityState
  checkedExercise <- mapLeft show $
    checkAuthorityExercise
      randomRequirement
      (PossessedCapability randomOccurrence)
      state
  context <- mapLeft show $
    registerCapabilityEnvironmentObservation
      randomRelation
      EnvironmentRandomness
      checkedExercise
      emptyEnvironmentObservationContext
  checked <- mapLeft show $
    checkEnvironmentObservation
      EnvironmentRandomness
      (ExplicitEnvironmentObservation randomRelation)
      context
  assert
    ( checkedEnvironmentObservationProvenance checked
        == EnvironmentCapabilityProvenance
            randomAuthorityContract randomAuthoritySubject randomAuthorityOperation
    )
    "checked capability observation lost exact authority relation"

otherExplicitRelationsAccept :: Either String ()
otherExplicitRelationsAccept = do
  context1 <- mapLeft show $
    registerEntryEnvironmentObservation
      entryRelation EnvironmentLocale "entry.request.locale" emptyEnvironmentObservationContext
  context2 <- mapLeft show $
    registerProtocolEnvironmentObservation
      protocolRelation EnvironmentWorkerIdentity "protocol.worker.assignment.v1" context1
  context3 <- mapLeft show $
    registerBoundaryEnvironmentObservation
      boundaryRelation (EnvironmentVariable "REQUEST_REGION") "boundary.request.region.v1" context2
  context4 <- mapLeft show $
    registerAssumptionEnvironmentObservation
      assumptionRelation EnvironmentSchedulerState "assumption.scheduler.class.v1" context3
  context5 <- mapLeft show $
    registerDeploymentEnvironmentObservation
      deploymentRelation (EnvironmentDeviceState "accelerator.model")
      "deployment.accelerator.v1" context4
  mapM_ (accept context5)
    [ (entryRelation, EnvironmentLocale, EnvironmentEntryProvenance "entry.request.locale")
    , (protocolRelation, EnvironmentWorkerIdentity,
        EnvironmentProtocolProvenance "protocol.worker.assignment.v1")
    , (boundaryRelation, EnvironmentVariable "REQUEST_REGION",
        EnvironmentBoundaryProvenance "boundary.request.region.v1")
    , (assumptionRelation, EnvironmentSchedulerState,
        EnvironmentAssumptionProvenance "assumption.scheduler.class.v1")
    , (deploymentRelation, EnvironmentDeviceState "accelerator.model",
        EnvironmentDeploymentProvenance "deployment.accelerator.v1")
    ]
  where
    accept context (key, kind, provenance) = do
      checked <- mapLeft show $
        checkEnvironmentObservation kind (ExplicitEnvironmentObservation key) context
      assert (checkedEnvironmentObservationProvenance checked == provenance)
        ("explicit environment provenance changed for " <> show key)

relationIdentityIsExact :: Either String ()
relationIdentityIsExact = do
  context <- mapLeft show $
    registerEntryEnvironmentObservation
      entryRelation EnvironmentLocale "entry.request.locale" emptyEnvironmentObservationContext
  let unknown = EnvironmentObservationRelationKey "exec011.environment.unknown"
  case checkEnvironmentObservation
      EnvironmentLocale
      (ExplicitEnvironmentObservation unknown)
      context of
    Left (UnknownEnvironmentObservationRelation actual) ->
      assert (actual == unknown) "unknown relation rejection lost identity"
    other -> Left ("unknown environmental relation was accepted: " <> show other)
  case registerEntryEnvironmentObservation
      entryRelation EnvironmentClockTime "entry.other" context of
    Left (DuplicateEnvironmentObservationRelation actual) ->
      assert (actual == entryRelation) "duplicate relation rejection lost identity"
    other -> Left ("duplicate environmental relation silently replaced prior meaning: " <> show other)

ambientKinds :: [EnvironmentObservationKind]
ambientKinds =
  [ EnvironmentClockTime
  , EnvironmentRandomness
  , EnvironmentVariable "HOME"
  , EnvironmentLocale
  , EnvironmentHostIdentity
  , EnvironmentProcessIdentity
  , EnvironmentThreadIdentity
  , EnvironmentWorkerIdentity
  , EnvironmentSchedulerState
  , EnvironmentFilesystemState "/tmp"
  , EnvironmentDeviceState "gpu.0"
  , EnvironmentOtherObservation "runtime.load-average"
  ]

clockRelation, randomRelation, entryRelation, protocolRelation :: EnvironmentObservationRelationKey
boundaryRelation, assumptionRelation, deploymentRelation :: EnvironmentObservationRelationKey
clockRelation = EnvironmentObservationRelationKey "exec011.clock.now"
randomRelation = EnvironmentObservationRelationKey "exec011.random.capability"
entryRelation = EnvironmentObservationRelationKey "exec011.entry.locale"
protocolRelation = EnvironmentObservationRelationKey "exec011.protocol.worker"
boundaryRelation = EnvironmentObservationRelationKey "exec011.boundary.env"
assumptionRelation = EnvironmentObservationRelationKey "exec011.assumption.scheduler"
deploymentRelation = EnvironmentObservationRelationKey "exec011.deployment.device"

clockProviderRevision :: InterfaceRevision
clockProviderRevision = InterfaceRevision "exec011.clock.provider.v1"

clockImplementationRevision :: DefinitionRevision
clockImplementationRevision = DefinitionRevision "exec011.clock.impl.v1"

clockOperation :: ProviderOperationKey
clockOperation = ProviderOperationKey "clock.now"

clockEntry :: ProviderImplementationEntryKey
clockEntry = ProviderImplementationEntryKey "impl.clock.now"

clockContractOutcome, clockImplementationOutcome :: ProviderOutcomeKey
clockContractOutcome = ProviderOutcomeKey "clock.now.success"
clockImplementationOutcome = ProviderOutcomeKey "impl.clock.now.success"

emptyResidue :: ProviderResourceResidue
emptyResidue = ProviderResourceResidue
  Set.empty Set.empty Set.empty Set.empty Set.empty

clockSurface :: CallableRefinementSurface
clockSurface = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "clock.now()->U64"
  , callableRefinementContract = CallableContract
      (InterfaceRevision "exec011.clock.call.v1") PreserveCallee Set.empty
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = Set.empty
  }

clockProviderContract :: ProviderContract
clockProviderContract = ProviderContract
  clockProviderRevision
  (Map.singleton clockOperation ProviderOperationContract
    { providerOperationCallableContract = clockSurface
    , providerOperationPreconditions = Set.empty
    , providerOperationOutcomeResidues = Map.singleton clockContractOutcome emptyResidue
    })

clockProviderImplementation :: ProviderImplementation
clockProviderImplementation = ProviderImplementation
  { providerImplementationDefinitionRevision = clockImplementationRevision
  , providerImplementationEntries = Map.singleton clockEntry ProviderImplementationOperation
      { providerImplementationCallable = clockSurface
      , providerImplementationPreconditions = Set.empty
      , providerImplementationOutcomeResidues =
          Map.singleton clockImplementationOutcome emptyResidue
      }
  , providerImplementationSymbols = Set.singleton "clock_gettime"
  }

clockProviderClaim :: ProviderQualificationClaim
clockProviderClaim = ProviderQualificationClaim
  { providerQualificationRequiredInterface = clockProviderRevision
  , providerQualificationImplementationRevision = clockImplementationRevision
  , providerQualificationOperationCorrespondences = Map.singleton clockOperation
      ProviderOperationCorrespondence
        { providerCorrespondenceImplementationEntry = clockEntry
        , providerCorrespondenceOutcomes =
            Map.singleton clockImplementationOutcome clockContractOutcome
        }
  }

clockProviderQualification :: Either String CheckedProviderSemanticQualification
clockProviderQualification = mapLeft show $
  checkProviderSemanticQualification
    clockProviderContract clockProviderImplementation clockProviderClaim

randomOccurrence :: CapabilityOccurrenceKey
randomOccurrence = CapabilityOccurrenceKey "exec011.random.capability.occurrence"

randomAuthorityContract :: AuthorityContractKey
randomAuthorityContract = AuthorityContractKey "exec011.random.authority.v1"

randomAuthoritySubject :: AuthoritySubjectKey
randomAuthoritySubject = AuthoritySubjectKey "exec011.random.source"

randomAuthorityOperation :: AuthorityOperationKey
randomAuthorityOperation = AuthorityOperationKey "observe"

randomRequirement :: AuthorityRequirement
randomRequirement = AuthorityRequirement
  randomAuthorityContract randomAuthoritySubject randomAuthorityOperation

randomCapability :: AuthorityCapability
randomCapability = AuthorityCapability
  { authorityCapabilityOccurrence = randomOccurrence
  , authorityCapabilityContract = randomAuthorityContract
  , authorityCapabilitySubject = randomAuthoritySubject
  , authorityCapabilityMode = Unrestricted
  , authorityCapabilityOperations = Set.singleton randomAuthorityOperation
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
