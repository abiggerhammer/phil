{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.CallableRefinement
import Phil.Core.ProviderLifecycleQualification
import Phil.Core.ProviderQualification
import Phil.Core.Static (DefinitionRevision (..), InterfaceRevision (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-008 valid lifecycle observations accepted" validLifecycleAccepted
    , test "PROV-008 forbidden partially committed state rejected" partialCommitRejected
    , test "PROV-008 wrong observation boundary rejected" wrongBoundaryRejected
    , test "PROV-008 cleanup residue mismatch rejected" cleanupMismatchRejected
    , test "PROV-008 retry disposition mismatch rejected" retryMismatchRejected
    , test "PROV-008 missing interruption point rejected" missingPointRejected
    , test "PROV-008 unexpected interruption point rejected" unexpectedPointRejected
    , test "PROV-008 interruption point must name qualified operation" unqualifiedOperationRejected
    , test "PROV-008 implementation may expose multiple allowed crash states" multipleAllowedStatesAccepted
    , test "PROV-008 ordering is nonsemantic" orderingCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validLifecycleAccepted :: Either String ()
validLifecycleAccepted = do
  qualified <- qualifiedProvider
  checked <- mapLeft show $ checkProviderLifecycleQualification qualified lifecycleContract validLifecycleModel
  assert (checkedProviderLifecycleObservationBoundary checked == clientBoundary)
    "checked lifecycle changed observation boundary"
  assert (checkedProviderLifecycleContractRevision checked == InterfaceRevision "provider.blob.v1")
    "checked lifecycle lost provider contract revision"

partialCommitRejected :: Either String ()
partialCommitRejected = do
  qualified <- qualifiedProvider
  let badObservation = cleanObservation { providerInterruptionObservableState = partialState }
      badModel = modelWith installWritePoint (Set.singleton badObservation)
  case checkProviderLifecycleQualification qualified lifecycleContract badModel of
    Left (ProviderLifecycleForbiddenObservableState point state) -> do
      assert (point == installWritePoint) "wrong interruption point for partial-state rejection"
      assert (state == partialState) "wrong forbidden state diagnostic"
    other -> Left ("partially committed state was accepted: " <> show other)

wrongBoundaryRejected :: Either String ()
wrongBoundaryRejected = do
  qualified <- qualifiedProvider
  let badObservation = cleanObservation
        { providerInterruptionObservationBoundary = internalBoundary }
      badModel = modelWith installWritePoint (Set.singleton badObservation)
  case checkProviderLifecycleQualification qualified lifecycleContract badModel of
    Left (ProviderLifecycleObservationBoundaryMismatch point expected actual) -> do
      assert (point == installWritePoint) "wrong interruption point for boundary mismatch"
      assert (expected == clientBoundary) "wrong expected observation boundary"
      assert (actual == internalBoundary) "wrong actual observation boundary"
    other -> Left ("internal observation boundary was accepted as client boundary: " <> show other)

cleanupMismatchRejected :: Either String ()
cleanupMismatchRejected = do
  qualified <- qualifiedProvider
  let badObservation = cleanObservation
        { providerInterruptionCleanupResidue = leakedTempResidue }
      badModel = modelWith installWritePoint (Set.singleton badObservation)
  case checkProviderLifecycleQualification qualified lifecycleContract badModel of
    Left (ProviderLifecycleForbiddenCleanupResidue point residue) -> do
      assert (point == installWritePoint) "wrong interruption point for cleanup mismatch"
      assert (residue == leakedTempResidue) "wrong cleanup residue diagnostic"
    other -> Left ("leaked crash residue was accepted: " <> show other)

retryMismatchRejected :: Either String ()
retryMismatchRejected = do
  qualified <- qualifiedProvider
  let badObservation = cleanObservation
        { providerInterruptionRetryDisposition = ProviderRetryForbidden }
      badModel = modelWith installWritePoint (Set.singleton badObservation)
  case checkProviderLifecycleQualification qualified lifecycleContract badModel of
    Left (ProviderLifecycleForbiddenRetryDisposition point retry) -> do
      assert (point == installWritePoint) "wrong interruption point for retry mismatch"
      assert (retry == ProviderRetryForbidden) "wrong retry diagnostic"
    other -> Left ("forbidden retry policy was accepted: " <> show other)

missingPointRejected :: Either String ()
missingPointRejected = do
  qualified <- qualifiedProvider
  let badModel = ProviderLifecycleModel
        (Map.singleton installWritePoint (Set.singleton cleanObservation))
  case checkProviderLifecycleQualification qualified lifecycleContract badModel of
    Left (ProviderLifecycleMissingInterruptionPoints missing) ->
      assert (missing == Set.singleton installPublishPoint)
        "wrong missing interruption point set"
    other -> Left ("missing lifecycle point was accepted: " <> show other)

unexpectedPointRejected :: Either String ()
unexpectedPointRejected = do
  qualified <- qualifiedProvider
  let extraPoint = ProviderLifecyclePoint installOperation (ProviderInterruptionPointKey "after-return")
      observations = Map.insert extraPoint (Set.singleton cleanObservation)
        (providerLifecycleImplementationObservations validLifecycleModel)
      badModel = ProviderLifecycleModel observations
  case checkProviderLifecycleQualification qualified lifecycleContract badModel of
    Left (ProviderLifecycleUnexpectedInterruptionPoints unexpected) ->
      assert (unexpected == Set.singleton extraPoint) "wrong unexpected point set"
    other -> Left ("unexpected lifecycle point was accepted: " <> show other)

unqualifiedOperationRejected :: Either String ()
unqualifiedOperationRejected = do
  qualified <- qualifiedProvider
  let deleteOperation = ProviderOperationKey "provider.op.delete"
      badPoint = ProviderLifecyclePoint deleteOperation (ProviderInterruptionPointKey "during-delete")
      badContract = lifecycleContract
        { providerLifecycleAllowances = Map.singleton badPoint cleanAllowance }
      badModel = ProviderLifecycleModel (Map.singleton badPoint (Set.singleton cleanObservation))
  case checkProviderLifecycleQualification qualified badContract badModel of
    Left (ProviderLifecycleUnqualifiedOperation point) ->
      assert (point == badPoint) "wrong unqualified lifecycle point"
    other -> Left ("unqualified operation lifecycle point was accepted: " <> show other)

multipleAllowedStatesAccepted :: Either String ()
multipleAllowedStatesAccepted = do
  qualified <- qualifiedProvider
  let allowance = cleanAllowance
        { providerLifecycleAllowedObservableStates = Set.fromList [absentState, completeState] }
      contract = lifecycleContract
        { providerLifecycleAllowances = Map.insert installWritePoint allowance
            (providerLifecycleAllowances lifecycleContract) }
      observations = Set.fromList
        [ cleanObservation { providerInterruptionObservableState = absentState }
        , cleanObservation { providerInterruptionObservableState = completeState }
        ]
      model = modelWith installWritePoint observations
  _ <- mapLeft show $ checkProviderLifecycleQualification qualified contract model
  Right ()

orderingCanonical :: Either String ()
orderingCanonical = do
  qualified <- qualifiedProvider
  let left = validLifecycleModel
      right = ProviderLifecycleModel (Map.fromList (reverse (Map.toAscList
        (providerLifecycleImplementationObservations validLifecycleModel))))
  checkedLeft <- mapLeft show $ checkProviderLifecycleQualification qualified lifecycleContract left
  checkedRight <- mapLeft show $ checkProviderLifecycleQualification qualified lifecycleContract right
  assert (checkedLeft == checkedRight) "lifecycle map ordering changed semantics"

modelWith
  :: ProviderLifecyclePoint
  -> Set.Set ProviderInterruptionObservation
  -> ProviderLifecycleModel
modelWith point replacements = ProviderLifecycleModel
  (Map.insert point replacements
    (providerLifecycleImplementationObservations validLifecycleModel))

lifecycleContract :: ProviderLifecycleContract
lifecycleContract = ProviderLifecycleContract
  { providerLifecycleRevision = ProviderLifecycleRevision "provider.lifecycle.blob.v1"
  , providerLifecycleObservationBoundary = clientBoundary
  , providerLifecycleAllowances = Map.fromList
      [ (installWritePoint, cleanAllowance)
      , (installPublishPoint, cleanAllowance)
      ]
  }

cleanAllowance :: ProviderLifecycleAllowance
cleanAllowance = ProviderLifecycleAllowance
  { providerLifecycleAllowedObservableStates = Set.fromList [absentState, completeState]
  , providerLifecycleAllowedCleanupResidues = Set.singleton emptyResidue
  , providerLifecycleAllowedRetryDispositions = Set.singleton ProviderRetrySameOperation
  }

validLifecycleModel :: ProviderLifecycleModel
validLifecycleModel = ProviderLifecycleModel (Map.fromList
  [ (installWritePoint, Set.singleton cleanObservation)
  , (installPublishPoint, Set.singleton
      (cleanObservation { providerInterruptionObservableState = completeState }))
  ])

cleanObservation :: ProviderInterruptionObservation
cleanObservation = ProviderInterruptionObservation
  { providerInterruptionObservationBoundary = clientBoundary
  , providerInterruptionObservableState = absentState
  , providerInterruptionCleanupResidue = emptyResidue
  , providerInterruptionRetryDisposition = ProviderRetrySameOperation
  }

clientBoundary, internalBoundary :: ProviderObservationBoundaryKey
clientBoundary = ProviderObservationBoundaryKey "client-visible-store"
internalBoundary = ProviderObservationBoundaryKey "temporary-file-directory"

installWritePoint, installPublishPoint :: ProviderLifecyclePoint
installWritePoint = ProviderLifecyclePoint installOperation
  (ProviderInterruptionPointKey "after-temp-write-before-publish")
installPublishPoint = ProviderLifecyclePoint installOperation
  (ProviderInterruptionPointKey "after-publish-before-return")

absentState, completeState, partialState :: ProviderObservableStateKey
absentState = ProviderObservableStateKey "absent"
completeState = ProviderObservableStateKey "complete"
partialState = ProviderObservableStateKey "partially-committed"

emptyResidue, leakedTempResidue :: ProviderResourceResidue
emptyResidue = ProviderResourceResidue Set.empty Set.empty Set.empty Set.empty Set.empty
leakedTempResidue = ProviderResourceResidue
  Set.empty Set.empty Set.empty Set.empty (Set.singleton (ProviderResourceKey "temp-file"))

qualifiedProvider :: Either String CheckedProviderSemanticQualification
qualifiedProvider = mapLeft show $
  checkProviderSemanticQualification providerContract providerImplementation providerClaim

providerContract :: ProviderContract
providerContract = ProviderContract
  { providerContractInterfaceRevision = InterfaceRevision "provider.blob.v1"
  , providerContractOperations = Map.singleton installOperation ProviderOperationContract
      { providerOperationCallableContract = callableSurface (InterfaceRevision "call.install.contract.v1")
      , providerOperationPreconditions = Set.empty
      , providerOperationOutcomeResidues = Map.fromList
          [ (installedOutcome, emptyResidue)
          , (existsOutcome, emptyResidue)
          ]
      }
  }

providerImplementation :: ProviderImplementation
providerImplementation = ProviderImplementation
  { providerImplementationDefinitionRevision = DefinitionRevision "provider.blob.impl.v1"
  , providerImplementationEntries = Map.singleton installEntry ProviderImplementationOperation
      { providerImplementationCallable = callableSurface (InterfaceRevision "call.install.impl.v1")
      , providerImplementationPreconditions = Set.empty
      , providerImplementationOutcomeResidues = Map.fromList
          [ (implInstalledOutcome, emptyResidue)
          , (implExistsOutcome, emptyResidue)
          ]
      }
  , providerImplementationSymbols = Set.singleton "blob_install"
  }

providerClaim :: ProviderQualificationClaim
providerClaim = ProviderQualificationClaim
  { providerQualificationRequiredInterface = InterfaceRevision "provider.blob.v1"
  , providerQualificationImplementationRevision = DefinitionRevision "provider.blob.impl.v1"
  , providerQualificationOperationCorrespondences = Map.singleton installOperation
      ProviderOperationCorrespondence
        { providerCorrespondenceImplementationEntry = installEntry
        , providerCorrespondenceOutcomes = Map.fromList
            [ (implInstalledOutcome, installedOutcome)
            , (implExistsOutcome, existsOutcome)
            ]
        }
  }

callableSurface :: InterfaceRevision -> CallableRefinementSurface
callableSurface revision = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "unit->unit"
  , callableRefinementContract = CallableContract
      { callableContractInterfaceRevision = revision
      , callableContractCalleeTransition = PreserveCallee
      , callableContractEffectBound = Set.empty
      }
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = Set.empty
  }

installOperation :: ProviderOperationKey
installOperation = ProviderOperationKey "provider.op.install-if-absent"

installEntry :: ProviderImplementationEntryKey
installEntry = ProviderImplementationEntryKey "impl.entry.install"

installedOutcome, existsOutcome, implInstalledOutcome, implExistsOutcome :: ProviderOutcomeKey
installedOutcome = ProviderOutcomeKey "contract.installed"
existsOutcome = ProviderOutcomeKey "contract.already-exists"
implInstalledOutcome = ProviderOutcomeKey "impl.installed"
implExistsOutcome = ProviderOutcomeKey "impl.exists"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
