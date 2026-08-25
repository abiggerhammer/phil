{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.CallableRefinement
import Phil.Core.ProviderLawQualification
import Phil.Core.ProviderQualification
import Phil.Core.Static (DefinitionRevision (..), InterfaceRevision (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-007 valid provider history satisfies no-replace law" validHistoryAccepted
    , test "PROV-007 individually valid operations can violate cross-operation law" repeatedInstallRejected
    , test "PROV-007 read-before-publish law violation rejects" readBeforePublishRejected
    , test "PROV-007 implementation outcomes translate through qualified correspondence" outcomeTranslationIsSemantic
    , test "PROV-007 unqualified operation rejects" unqualifiedOperationRejects
    , test "PROV-007 unmapped implementation outcome rejects" unmappedOutcomeRejects
    , test "PROV-007 violation identifies exact law state, event, and index" violationDiagnosticIsExact
    , test "PROV-007 empty history remains at initial law state" emptyTraceAccepted
    , test "PROV-007 law corpus key ordering is nonsemantic" corpusOrderingIsCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validHistoryAccepted :: Either String ()
validHistoryAccepted = do
  qualified <- qualifiedProvider
  checked <- mapLeft show $ checkProviderLawTrace qualified noReplaceLaw
    [ installInstalledEvent
    , readFoundEvent
    , installExistsEvent
    , readFoundEvent
    ]
  assert (checkedProviderLawFinalState checked == fullState)
    "valid history ended in wrong law state"

repeatedInstallRejected :: Either String ()
repeatedInstallRejected = do
  qualified <- qualifiedProvider
  -- Both implementation events are individually admitted by the exact
  -- PROV-001--005 operation qualification. Only their sequence is illegal.
  _ <- mapLeft show $ checkProviderLawTrace qualified noReplaceLaw [installInstalledEvent]
  case checkProviderLawTrace qualified noReplaceLaw
      [installInstalledEvent, installInstalledEvent] of
    Left (ProviderLawViolation revision 1 state event) -> do
      assert (revision == noReplaceLawRevision) "wrong law revision"
      assert (state == fullState) "second install rejected from wrong state"
      assert (event == ProviderPublicEvent installOperation installedOutcome)
        "wrong public event in repeated-install violation"
    other -> Left ("repeated successful install did not violate law: " <> show other)

readBeforePublishRejected :: Either String ()
readBeforePublishRejected = do
  qualified <- qualifiedProvider
  case checkProviderLawTrace qualified noReplaceLaw [readFoundEvent] of
    Left (ProviderLawViolation _ 0 state event) -> do
      assert (state == emptyState) "read-before-publish rejected from wrong state"
      assert (event == ProviderPublicEvent readOperation foundOutcome)
        "wrong read-before-publish public event"
    other -> Left ("read-before-publish was accepted: " <> show other)

outcomeTranslationIsSemantic :: Either String ()
outcomeTranslationIsSemantic = do
  qualified <- qualifiedProvider
  checked <- mapLeft show $ checkProviderLawTrace qualified noReplaceLaw
    [installInstalledEvent, installExistsEvent]
  assert
    (checkedProviderLawPublicTrace checked ==
      [ ProviderPublicEvent installOperation installedOutcome
      , ProviderPublicEvent installOperation existsOutcome
      ])
    "implementation outcome keys leaked past semantic correspondence"

unqualifiedOperationRejects :: Either String ()
unqualifiedOperationRejects = do
  qualified <- qualifiedProvider
  let unknownOperation = ProviderOperationKey "provider.op.delete"
      event = ProviderImplementationEvent unknownOperation implInstalledOutcome
  case checkProviderLawTrace qualified noReplaceLaw [event] of
    Left (ProviderLawTraceUsesUnqualifiedOperation operation) ->
      assert (operation == unknownOperation) "wrong unqualified operation diagnostic"
    other -> Left ("unqualified provider operation was accepted: " <> show other)

unmappedOutcomeRejects :: Either String ()
unmappedOutcomeRejects = do
  qualified <- qualifiedProvider
  let unknownOutcome = ProviderOutcomeKey "impl.outcome.corrupt"
      event = ProviderImplementationEvent installOperation unknownOutcome
  case checkProviderLawTrace qualified noReplaceLaw [event] of
    Left (ProviderLawTraceUsesUnmappedImplementationOutcome operation outcome) -> do
      assert (operation == installOperation) "wrong operation for unmapped outcome"
      assert (outcome == unknownOutcome) "wrong unmapped outcome diagnostic"
    other -> Left ("unmapped implementation outcome was accepted: " <> show other)

violationDiagnosticIsExact :: Either String ()
violationDiagnosticIsExact = do
  qualified <- qualifiedProvider
  case checkProviderLawTrace qualified noReplaceLaw
      [installInstalledEvent, readFoundEvent, installInstalledEvent] of
    Left (ProviderLawViolation revision index state event) -> do
      assert (revision == noReplaceLawRevision) "wrong violation law revision"
      assert (index == 2) "wrong zero-based violation index"
      assert (state == fullState) "wrong violation pre-state"
      assert (event == ProviderPublicEvent installOperation installedOutcome)
        "wrong violation event"
    other -> Left ("expected exact law violation: " <> show other)

emptyTraceAccepted :: Either String ()
emptyTraceAccepted = do
  qualified <- qualifiedProvider
  checked <- mapLeft show $ checkProviderLawTrace qualified noReplaceLaw []
  assert (checkedProviderLawFinalState checked == emptyState)
    "empty history changed law state"

corpusOrderingIsCanonical :: Either String ()
corpusOrderingIsCanonical = do
  qualified <- qualifiedProvider
  let traceA = ProviderImplementationTraceKey "a"
      traceB = ProviderImplementationTraceKey "b"
      left = Map.fromList
        [ (traceA, [installInstalledEvent])
        , (traceB, [readMissingEvent])
        ]
      right = Map.fromList
        [ (traceB, [readMissingEvent])
        , (traceA, [installInstalledEvent])
        ]
  checkedLeft <- mapLeft show $ checkProviderLawCorpus qualified noReplaceLaw left
  checkedRight <- mapLeft show $ checkProviderLawCorpus qualified noReplaceLaw right
  assert (checkedLeft == checkedRight) "trace-map insertion order changed law semantics"

qualifiedProvider :: Either String CheckedProviderSemanticQualification
qualifiedProvider = mapLeft show $
  checkProviderSemanticQualification providerContract providerImplementation providerClaim

providerContract :: ProviderContract
providerContract = ProviderContract
  { providerContractInterfaceRevision = InterfaceRevision "provider.blob.v1"
  , providerContractOperations = Map.fromList
      [ (installOperation, ProviderOperationContract
          { providerOperationCallableContract = callableSurface "call.install.contract.v1"
          , providerOperationPreconditions = Set.empty
          , providerOperationOutcomeResidues = Map.fromList
              [ (installedOutcome, emptyResidue)
              , (existsOutcome, emptyResidue)
              ]
          })
      , (readOperation, ProviderOperationContract
          { providerOperationCallableContract = callableSurface "call.read.contract.v1"
          , providerOperationPreconditions = Set.empty
          , providerOperationOutcomeResidues = Map.fromList
              [ (foundOutcome, emptyResidue)
              , (missingOutcome, emptyResidue)
              ]
          })
      ]
  }

providerImplementation :: ProviderImplementation
providerImplementation = ProviderImplementation
  { providerImplementationDefinitionRevision = DefinitionRevision "provider.blob.impl.v1"
  , providerImplementationEntries = Map.fromList
      [ (installEntry, ProviderImplementationOperation
          { providerImplementationCallable = callableSurface "call.install.impl.v1"
          , providerImplementationPreconditions = Set.empty
          , providerImplementationOutcomeResidues = Map.fromList
              [ (implInstalledOutcome, emptyResidue)
              , (implExistsOutcome, emptyResidue)
              ]
          })
      , (readEntry, ProviderImplementationOperation
          { providerImplementationCallable = callableSurface "call.read.impl.v1"
          , providerImplementationPreconditions = Set.empty
          , providerImplementationOutcomeResidues = Map.fromList
              [ (implFoundOutcome, emptyResidue)
              , (implMissingOutcome, emptyResidue)
              ]
          })
      ]
  , providerImplementationSymbols = Set.fromList ["blob_install", "blob_read"]
  }

providerClaim :: ProviderQualificationClaim
providerClaim = ProviderQualificationClaim
  { providerQualificationRequiredInterface = InterfaceRevision "provider.blob.v1"
  , providerQualificationImplementationRevision = DefinitionRevision "provider.blob.impl.v1"
  , providerQualificationOperationCorrespondences = Map.fromList
      [ (installOperation, ProviderOperationCorrespondence
          { providerCorrespondenceImplementationEntry = installEntry
          , providerCorrespondenceOutcomes = Map.fromList
              [ (implInstalledOutcome, installedOutcome)
              , (implExistsOutcome, existsOutcome)
              ]
          })
      , (readOperation, ProviderOperationCorrespondence
          { providerCorrespondenceImplementationEntry = readEntry
          , providerCorrespondenceOutcomes = Map.fromList
              [ (implFoundOutcome, foundOutcome)
              , (implMissingOutcome, missingOutcome)
              ]
          })
      ]
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

emptyResidue :: ProviderResourceResidue
emptyResidue = ProviderResourceResidue Set.empty Set.empty Set.empty Set.empty Set.empty

installOperation, readOperation :: ProviderOperationKey
installOperation = ProviderOperationKey "provider.op.install-if-absent"
readOperation = ProviderOperationKey "provider.op.read"

installEntry, readEntry :: ProviderImplementationEntryKey
installEntry = ProviderImplementationEntryKey "impl.entry.install"
readEntry = ProviderImplementationEntryKey "impl.entry.read"

installedOutcome, existsOutcome, foundOutcome, missingOutcome :: ProviderOutcomeKey
installedOutcome = ProviderOutcomeKey "contract.installed"
existsOutcome = ProviderOutcomeKey "contract.already-exists"
foundOutcome = ProviderOutcomeKey "contract.found"
missingOutcome = ProviderOutcomeKey "contract.missing"

implInstalledOutcome, implExistsOutcome, implFoundOutcome, implMissingOutcome :: ProviderOutcomeKey
implInstalledOutcome = ProviderOutcomeKey "impl.installed"
implExistsOutcome = ProviderOutcomeKey "impl.exists"
implFoundOutcome = ProviderOutcomeKey "impl.found"
implMissingOutcome = ProviderOutcomeKey "impl.missing"

installInstalledEvent, installExistsEvent, readFoundEvent, readMissingEvent
  :: ProviderImplementationEvent
installInstalledEvent = ProviderImplementationEvent installOperation implInstalledOutcome
installExistsEvent = ProviderImplementationEvent installOperation implExistsOutcome
readFoundEvent = ProviderImplementationEvent readOperation implFoundOutcome
readMissingEvent = ProviderImplementationEvent readOperation implMissingOutcome

noReplaceLawRevision :: ProviderLawRevision
noReplaceLawRevision = ProviderLawRevision "provider-law.no-replace.v1"

emptyState, fullState :: ProviderLawStateKey
emptyState = ProviderLawStateKey "empty"
fullState = ProviderLawStateKey "full"

noReplaceLaw :: ProviderLaw
noReplaceLaw = ProviderLaw
  { providerLawRevision = noReplaceLawRevision
  , providerLawInitialState = emptyState
  , providerLawTransitions = Map.fromList
      [ ((emptyState, ProviderPublicEvent installOperation installedOutcome), fullState)
      , ((emptyState, ProviderPublicEvent readOperation missingOutcome), emptyState)
      , ((fullState, ProviderPublicEvent installOperation existsOutcome), fullState)
      , ((fullState, ProviderPublicEvent readOperation foundOutcome), fullState)
      ]
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
