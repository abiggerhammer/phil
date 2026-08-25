{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.CallableRefinement
import Phil.Core.ProviderQualification
import Phil.Core.ProviderStateQualification
import Phil.Core.Static (DefinitionRevision (..), InterfaceRevision (..))
import Phil.Core.Syntax (Outcome (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-006 stateful provider simulation accepts" validSimulationAccepts
    , test "PROV-006 every visible implementation initial state is mapped" missingInitialRejects
    , test "PROV-006 initialization mapping has exact visible-state domain" unexpectedInitialRejects
    , test "PROV-006 initial abstract state must be admissible" inadmissibleInitialRejects
    , test "PROV-006 initial pair must satisfy the named relation" initialPairOutsideRelationRejects
    , test "PROV-006 transition operation must already be semantically qualified" unqualifiedOperationRejects
    , test "PROV-006 implementation outcome must use checked outcome correspondence" unmappedOutcomeRejects
    , test "PROV-006 reachable implementation pre-state must be related" unrelatedPreStateRejects
    , test "PROV-006 implementation transition must simulate a contract transition" missingSimulationRejects
    , test "PROV-006 successor implementation state must remain related" unrelatedSuccessorRejects
    , test "PROV-006 state simulation uses public mapped outcome identity" publicOutcomeMappingIsUsed
    , test "PROV-006 implementation may realize fewer abstract transitions" narrowerImplementationAccepts
    , test "PROV-006 every abstract state related to a concrete pre-state is simulated" allRelatedPreStatesMustSimulate
    , test "PROV-006 relation and transition ordering is nonsemantic" orderingIsCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validSimulationAccepts :: Either String ()
validSimulationAccepts = do
  checked <- checkedProvider
  result <- mapLeft show $ checkProviderStateSimulation checked baseRefinement
  assert (checkedProviderStateRelationRevision result == relationRevision)
    "checked simulation lost relation revision"
  assert (checkedProviderStateInitialization result == initialMap)
    "checked simulation changed initialization mapping"

missingInitialRejects :: Either String ()
missingInitialRejects = do
  checked <- checkedProvider
  let bad = baseRefinement { providerStateInitialCorrespondence = Map.empty }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateMissingInitialCorrespondence missing) ->
      assert (missing == Set.singleton implEmpty) "wrong missing initial state"
    other -> Left ("missing initial correspondence did not reject: " <> show other)

unexpectedInitialRejects :: Either String ()
unexpectedInitialRejects = do
  checked <- checkedProvider
  let bad = baseRefinement
        { providerStateInitialCorrespondence = Map.insert implFull absFull initialMap }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateUnexpectedInitialCorrespondence unexpected) ->
      assert (unexpected == Set.singleton implFull) "wrong unexpected initial state"
    other -> Left ("unexpected initial correspondence did not reject: " <> show other)

inadmissibleInitialRejects :: Either String ()
inadmissibleInitialRejects = do
  checked <- checkedProvider
  let bad = baseRefinement
        { providerStateAdmissibleInitialAbstractStates = Set.singleton absFull }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateInitialAbstractStateNotAdmissible implementationState abstractState) -> do
      assert (implementationState == implEmpty) "wrong implementation initial state"
      assert (abstractState == absEmpty) "wrong abstract initial state"
    other -> Left ("inadmissible initial state did not reject: " <> show other)

initialPairOutsideRelationRejects :: Either String ()
initialPairOutsideRelationRejects = do
  checked <- checkedProvider
  let bad = baseRefinement
        { providerStateRelatedPairs = Set.delete (ProviderStatePair implEmpty absEmpty) basePairs }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateInitialPairOutsideRelation implementationState abstractState) -> do
      assert (implementationState == implEmpty) "wrong implementation initial pair"
      assert (abstractState == absEmpty) "wrong abstract initial pair"
    other -> Left ("initial pair outside relation did not reject: " <> show other)

unqualifiedOperationRejects :: Either String ()
unqualifiedOperationRejects = do
  checked <- checkedProvider
  let badTransition = ProviderImplementationStateTransition
        deleteOperation implEmpty implStored implFull
      bad = baseRefinement
        { providerStateImplementationTransitions = Set.singleton badTransition }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateTransitionUsesUnqualifiedOperation operation) ->
      assert (operation == deleteOperation) "wrong unqualified operation"
    other -> Left ("unqualified transition operation did not reject: " <> show other)

unmappedOutcomeRejects :: Either String ()
unmappedOutcomeRejects = do
  checked <- checkedProvider
  let badTransition = ProviderImplementationStateTransition
        putOperation implEmpty implUnknown implFull
      bad = baseRefinement
        { providerStateImplementationTransitions = Set.singleton badTransition }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateTransitionUsesUnmappedImplementationOutcome operation outcome) -> do
      assert (operation == putOperation) "wrong operation for unmapped outcome"
      assert (outcome == implUnknown) "wrong unmapped implementation outcome"
    other -> Left ("unmapped implementation outcome did not reject: " <> show other)

unrelatedPreStateRejects :: Either String ()
unrelatedPreStateRejects = do
  checked <- checkedProvider
  let transition = ProviderImplementationStateTransition
        putOperation implUnknownState implStored implFull
      bad = baseRefinement
        { providerStateImplementationTransitions = Set.singleton transition }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateTransitionStartsOutsideRelation actual) ->
      assert (actual == transition) "wrong unrelated transition"
    other -> Left ("unrelated implementation pre-state did not reject: " <> show other)

missingSimulationRejects :: Either String ()
missingSimulationRejects = do
  checked <- checkedProvider
  let transition = ProviderImplementationStateTransition
        putOperation implEmpty implStored implFull
      bad = baseRefinement
        { providerStateImplementationTransitions = Set.singleton transition
        , providerStateContractTransitions = Set.empty
        }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateTransitionNotSimulated actual abstractPre publicOutcome) -> do
      assert (actual == transition) "wrong unsimulated transition"
      assert (abstractPre == absEmpty) "wrong abstract pre-state"
      assert (publicOutcome == publicStored) "wrong public mapped outcome"
    other -> Left ("missing state simulation did not reject: " <> show other)

unrelatedSuccessorRejects :: Either String ()
unrelatedSuccessorRejects = do
  checked <- checkedProvider
  let transition = ProviderImplementationStateTransition
        putOperation implEmpty implStored implUnknownState
      bad = baseRefinement
        { providerStateImplementationTransitions = Set.singleton transition }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateTransitionNotSimulated actual abstractPre publicOutcome) -> do
      assert (actual == transition) "wrong successor transition"
      assert (abstractPre == absEmpty) "wrong successor abstract pre-state"
      assert (publicOutcome == publicStored) "wrong successor public outcome"
    other -> Left ("unrelated successor state did not reject: " <> show other)

publicOutcomeMappingIsUsed :: Either String ()
publicOutcomeMappingIsUsed = do
  checked <- checkedProvider
  let wrongAbstractTransition = ProviderContractStateTransition
        putOperation absEmpty implStored absFull
      transition = ProviderImplementationStateTransition
        putOperation implEmpty implStored implFull
      bad = baseRefinement
        { providerStateImplementationTransitions = Set.singleton transition
        , providerStateContractTransitions = Set.singleton wrongAbstractTransition
        }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateTransitionNotSimulated _ _ publicOutcome) ->
      assert (publicOutcome == publicStored)
        "state simulation used implementation outcome instead of public mapping"
    other -> Left ("implementation outcome identity bypassed public mapping: " <> show other)

narrowerImplementationAccepts :: Either String ()
narrowerImplementationAccepts = do
  checked <- checkedProvider
  let onlyStore = Set.singleton $ ProviderImplementationStateTransition
        putOperation implEmpty implStored implFull
      richerContract = Set.insert
        (ProviderContractStateTransition putOperation absEmpty publicExists absEmpty)
        baseContractTransitions
      refinement = baseRefinement
        { providerStateImplementationTransitions = onlyStore
        , providerStateContractTransitions = richerContract
        }
  _ <- mapLeft show $ checkProviderStateSimulation checked refinement
  Right ()

allRelatedPreStatesMustSimulate :: Either String ()
allRelatedPreStatesMustSimulate = do
  checked <- checkedProvider
  let aliasPair = ProviderStatePair implEmpty absEmptyAlias
      transition = ProviderImplementationStateTransition
        putOperation implEmpty implStored implFull
      bad = baseRefinement
        { providerStateRelatedPairs = Set.insert aliasPair basePairs
        , providerStateImplementationTransitions = Set.singleton transition
        }
  case checkProviderStateSimulation checked bad of
    Left (ProviderStateTransitionNotSimulated actual abstractPre publicOutcome) -> do
      assert (actual == transition) "wrong multiply-related transition"
      assert (abstractPre == absEmptyAlias) "wrong unsimulated related abstract pre-state"
      assert (publicOutcome == publicStored) "wrong multiply-related public outcome"
    other -> Left ("one related abstract pre-state was silently ignored: " <> show other)

orderingIsCanonical :: Either String ()
orderingIsCanonical = do
  checked <- checkedProvider
  let reversed = baseRefinement
        { providerStateRelatedPairs = Set.fromList (reverse (Set.toAscList basePairs))
        , providerStateImplementationTransitions =
            Set.fromList (reverse (Set.toAscList baseImplementationTransitions))
        , providerStateContractTransitions =
            Set.fromList (reverse (Set.toAscList baseContractTransitions))
        }
  left <- mapLeft show $ checkProviderStateSimulation checked baseRefinement
  right <- mapLeft show $ checkProviderStateSimulation checked reversed
  assert (left == right) "state relation/transition enumeration changed semantics"

checkedProvider :: Either String CheckedProviderSemanticQualification
checkedProvider = mapLeft show $
  checkProviderSemanticQualification providerContract providerImplementation providerClaim

providerContract :: ProviderContract
providerContract = ProviderContract
  { providerContractInterfaceRevision = providerInterface
  , providerContractOperations = Map.singleton putOperation putContract
  }

providerImplementation :: ProviderImplementation
providerImplementation = ProviderImplementation
  { providerImplementationDefinitionRevision = providerDefinition
  , providerImplementationEntries = Map.singleton putEntry putImplementation
  , providerImplementationSymbols = Set.singleton "store_put"
  }

providerClaim :: ProviderQualificationClaim
providerClaim = ProviderQualificationClaim
  { providerQualificationRequiredInterface = providerInterface
  , providerQualificationImplementationRevision = providerDefinition
  , providerQualificationOperationCorrespondences = Map.singleton putOperation
      (ProviderOperationCorrespondence putEntry (Map.fromList
        [ (implStored, publicStored)
        , (implExists, publicExists)
        ]))
  }

putContract :: ProviderOperationContract
putContract = ProviderOperationContract
  { providerOperationCallableContract = callableSurface
  , providerOperationPreconditions = Set.empty
  , providerOperationOutcomeResidues = Map.fromList
      [ (publicStored, emptyResidue)
      , (publicExists, emptyResidue)
      ]
  }

putImplementation :: ProviderImplementationOperation
putImplementation = ProviderImplementationOperation
  { providerImplementationCallable = callableSurface
  , providerImplementationPreconditions = Set.empty
  , providerImplementationOutcomeResidues = Map.fromList
      [ (implStored, emptyResidue)
      , (implExists, emptyResidue)
      ]
  }

callableSurface :: CallableRefinementSurface
callableSurface = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "store-put(bytes)->result"
  , callableRefinementContract = CallableContract
      { callableContractInterfaceRevision = InterfaceRevision "callable.store-put.v1"
      , callableContractCalleeTransition = PreserveCallee
      , callableContractEffectBound = Set.singleton (SemanticEffect "storage.write")
      }
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = Set.singleton
      (CallableTypedNegative (Outcome "already-exists"))
  }

emptyResidue :: ProviderResourceResidue
emptyResidue = ProviderResourceResidue Set.empty Set.empty Set.empty Set.empty Set.empty

providerInterface :: InterfaceRevision
providerInterface = InterfaceRevision "provider.store.v1"

providerDefinition :: DefinitionRevision
providerDefinition = DefinitionRevision "provider.store.impl.v1"

putOperation, deleteOperation :: ProviderOperationKey
putOperation = ProviderOperationKey "put"
deleteOperation = ProviderOperationKey "delete"

putEntry :: ProviderImplementationEntryKey
putEntry = ProviderImplementationEntryKey "impl.put"

publicStored, publicExists, implStored, implExists, implUnknown :: ProviderOutcomeKey
publicStored = ProviderOutcomeKey "stored"
publicExists = ProviderOutcomeKey "already-exists"
implStored = ProviderOutcomeKey "impl-stored"
implExists = ProviderOutcomeKey "impl-exists"
implUnknown = ProviderOutcomeKey "impl-unknown"

relationRevision :: ProviderStateRelationRevision
relationRevision = ProviderStateRelationRevision "state.store.v1"

absEmpty, absFull, absEmptyAlias :: ProviderAbstractStateKey
absEmpty = ProviderAbstractStateKey "abstract.empty"
absFull = ProviderAbstractStateKey "abstract.full"
absEmptyAlias = ProviderAbstractStateKey "abstract.empty-alias"

implEmpty, implFull, implUnknownState :: ProviderImplementationStateKey
implEmpty = ProviderImplementationStateKey "implementation.empty"
implFull = ProviderImplementationStateKey "implementation.full"
implUnknownState = ProviderImplementationStateKey "implementation.unknown"

basePairs :: Set.Set ProviderStatePair
basePairs = Set.fromList
  [ ProviderStatePair implEmpty absEmpty
  , ProviderStatePair implFull absFull
  ]

initialMap :: Map.Map ProviderImplementationStateKey ProviderAbstractStateKey
initialMap = Map.singleton implEmpty absEmpty

baseImplementationTransitions :: Set.Set ProviderImplementationStateTransition
baseImplementationTransitions = Set.fromList
  [ ProviderImplementationStateTransition putOperation implEmpty implStored implFull
  , ProviderImplementationStateTransition putOperation implFull implExists implFull
  ]

baseContractTransitions :: Set.Set ProviderContractStateTransition
baseContractTransitions = Set.fromList
  [ ProviderContractStateTransition putOperation absEmpty publicStored absFull
  , ProviderContractStateTransition putOperation absFull publicExists absFull
  ]

baseRefinement :: ProviderStateRefinement
baseRefinement = ProviderStateRefinement
  { providerStateRelationRevision = relationRevision
  , providerStateRelatedPairs = basePairs
  , providerStateVisibleInitialImplementationStates = Set.singleton implEmpty
  , providerStateAdmissibleInitialAbstractStates = Set.singleton absEmpty
  , providerStateInitialCorrespondence = initialMap
  , providerStateImplementationTransitions = baseImplementationTransitions
  , providerStateContractTransitions = baseContractTransitions
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
