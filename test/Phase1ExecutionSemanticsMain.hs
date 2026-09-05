{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.Types (Digest (..))
import Phil.Surface.GrammarV1.Parser
  ( parseGrammarV1StructuralSource
  )
import Phil.Systems.IR
  ( StageContract (..)
  , ValueId (..)
  )
import Phil.Systems.SemanticInitialization
  ( CheckedSemanticInitializationTrace (..)
  , SemanticInitializationError (..)
  , SemanticInitializationEvent (..)
  , SemanticInitializationOrigin (..)
  , SemanticInitializationTrace (..)
  , SemanticObservationKind (..)
  , SemanticStorageKey (..)
  , checkSemanticInitializationTrace
  , renderSemanticInitializationTrace
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-005 source reassignment rejects while explicit successor bindings remain valid"
        immutableSourceBindings
    , test "EXEC-006 initialized semantic values may be observed only after exact establishment"
        initializedValuesAccept
    , test "EXEC-006 reserved target storage is not an initialized Phil value"
        reservedStorageDoesNotInitialize
    , test "EXEC-006 initialization into storage requires the exact prior reservation"
        initializationRequiresReservation
    , test "EXEC-005/006 one semantic value identity cannot be reinitialized in place"
        semanticValueReinitializationRejects
    , test "EXEC-006 initialization evidence must be bound into the exact StageContract"
        missingInitializationRelationRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

immutableSourceBindings :: Either String ()
immutableSourceBindings = do
  case parseGrammarV1StructuralSource "exec-005-mutation" mutationSource of
    Left _ -> Right ()
    Right parsed -> Left ("source assignment unexpectedly parsed: " <> show parsed)
  case parseGrammarV1StructuralSource "exec-005-successor" successorSource of
    Left diagnostic -> Left ("explicit successor bindings unexpectedly rejected: " <> show diagnostic)
    Right _ -> Right ()
  where
    mutationSource =
      "component Immutable(x : U32) { let y = x; y = 1; return y; }"
    successorSource =
      "component Immutable(x : U32) { let y = x; let z = y; return z; }"

initializedValuesAccept :: Either String ()
initializedValuesAccept = do
  let storage = SemanticStorageKey "storage.ready"
      storedValue = ValueId "value.ready"
      rootValue = ValueId "value.root"
      trace = baseTrace
        [ SemanticStorageReserved storage
        , SemanticValueInitialized storedValue (Just storage) SemanticProviderResult
        , SemanticValueObserved storedValue SemanticRead
        , SemanticValueObserved storedValue SemanticHash
        , SemanticValueObserved storedValue SemanticExport
        , SemanticValueInitialized rootValue Nothing SemanticRootInput
        , SemanticValueObserved rootValue SemanticCompare
        , SemanticValueObserved rootValue SemanticSerialize
        , SemanticValueObserved rootValue SemanticEvidenceUse
        ]
      contract = contractFor trace
  checked <- mapLeft show (checkSemanticInitializationTrace contract trace)
  assert
    (checkedSemanticInitializedValues checked == Set.fromList [storedValue, rootValue])
    "checked initialization lost or invented semantic value identities"
  assert
    (checkedSemanticReservedStorage checked == Set.singleton storage)
    "checked initialization lost or invented reserved semantic storage identity"

reservedStorageDoesNotInitialize :: Either String ()
reservedStorageDoesNotInitialize = do
  let storage = SemanticStorageKey "storage.uninitialized"
      value = ValueId "value.uninitialized"
      trace = baseTrace
        [ SemanticStorageReserved storage
        , SemanticValueObserved value SemanticRead
        ]
      contract = contractFor trace
  case checkSemanticInitializationTrace contract trace of
    Left (SemanticObservationBeforeInitialization actual SemanticRead) ->
      assert (actual == value)
        "uninitialized-read rejection lost the exact semantic value identity"
    other -> Left
      ("reserved target storage was treated as an initialized Phil value: " <> show other)

initializationRequiresReservation :: Either String ()
initializationRequiresReservation = do
  let storage = SemanticStorageKey "storage.missing"
      value = ValueId "value.missing-storage"
      trace = baseTrace
        [ SemanticValueInitialized value (Just storage) SemanticBoundaryValue
        ]
      contract = contractFor trace
  case checkSemanticInitializationTrace contract trace of
    Left (SemanticInitializationStorageNotReserved actualValue actualStorage) -> do
      assert (actualValue == value)
        "missing-reservation rejection lost the semantic value identity"
      assert (actualStorage == storage)
        "missing-reservation rejection lost the semantic storage identity"
    other -> Left
      ("semantic value initialized into unreserved storage: " <> show other)

semanticValueReinitializationRejects :: Either String ()
semanticValueReinitializationRejects = do
  let value = ValueId "value.immutable"
      trace = baseTrace
        [ SemanticValueInitialized value Nothing SemanticLiteralValue
        , SemanticValueInitialized value Nothing SemanticCallableResult
        ]
      contract = contractFor trace
  case checkSemanticInitializationTrace contract trace of
    Left (SemanticValueReinitialized actual) ->
      assert (actual == value)
        "reinitialization rejection lost the exact semantic value identity"
    other -> Left
      ("one semantic ValueId was initialized twice in place: " <> show other)

missingInitializationRelationRejects :: Either String ()
missingInitializationRelationRejects = do
  let value = ValueId "value.unbound-evidence"
      trace = baseTrace
        [ SemanticValueInitialized value Nothing SemanticRootInput
        , SemanticValueObserved value SemanticExport
        ]
      contract = (contractFor trace) { stageTraceRelation = [] }
      expected = renderSemanticInitializationTrace trace
  case checkSemanticInitializationTrace contract trace of
    Left (SemanticInitializationMissingTraceRelation actual) ->
      assert (actual == expected)
        "missing-relation rejection did not preserve the exact initialization trace"
    other -> Left
      ("unbound semantic initialization evidence was accepted: " <> show other)

baseTrace :: [SemanticInitializationEvent] -> SemanticInitializationTrace
baseTrace events = SemanticInitializationTrace
  { semanticInitializationStageContractId = "stage.exec.init"
  , semanticInitializationSourceDigest = Digest "source.exec.init"
  , semanticInitializationTargetDigest = Digest "target.exec.init"
  , semanticInitializationEvents = events
  }

contractFor :: SemanticInitializationTrace -> StageContract
contractFor trace = StageContract
  { stageContractId = semanticInitializationStageContractId trace
  , stageSourceArtifactDigest = semanticInitializationSourceDigest trace
  , stageTargetArtifactDigest = semanticInitializationTargetDigest trace
  , stageFacts = []
  , stageInvariants = Map.empty
  , stageRequiredEdges = []
  , stageDerivedObligations = []
  , stageAssumptions = []
  , stageTraceRelation = [renderSemanticInitializationTrace trace]
  , stageResourceFailureRelation = []
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
