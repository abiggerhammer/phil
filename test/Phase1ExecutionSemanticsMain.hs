{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.Types (Digest (..))
import Phil.Core.CheckedUIntArithmetic
  ( CheckedUIntArithmeticDecision (..)
  , CheckedUIntArithmeticError (..)
  , CheckedUIntArithmeticSuccess (..)
  , checkedUIntOverflowFailure
  , checkedUIntUnderflowFailure
  , checkCheckedUIntArithmetic
  )
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Discharge
  ( DischargeError (..)
  , emptyDischargePolicy
  , resolveObligation
  )
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , RefSort (..)
  , RefTerm (..)
  )
import Phil.Core.UIntArithmetic
  ( PlainUIntArithmeticDecision (..)
  , PlainUIntArithmeticSite (..)
  , UIntArithmeticError (..)
  , UIntArithmeticOperator (..)
  , checkPlainUIntArithmetic
  , plainUIntArithmeticProposition
  , registerUIntArithmeticClaims
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  , GrammarV1Type (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.RuntimeScalar
  ( GrammarV1RuntimeScalarError (..)
  , grammarV1ContextualUIntLiteral
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
    , test "EXEC-007 unsuffixed runtime integer literals use exact contextual UInt range"
        contextualUIntLiteralRange
    , test "EXEC-008 plain UInt arithmetic is exact or remains an explicit obligation"
        exactPlainUIntArithmetic
    , test "EXEC-009 checked UInt arithmetic exposes exact success and explicit range outcomes"
        checkedUIntArithmeticOutcomes
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

contextualUIntLiteralRange :: Either String ()
contextualUIntLiteralRange = do
  assert
    ( grammarV1ContextualUIntLiteral
        (GrammarV1UnsignedType "U8")
        (GrammarV1IntegerExpression "0")
        == Right (ScalarUIntLiteral 8 0)
    )
    "U8 zero did not elaborate to exact Core scalar identity"
  assert
    ( grammarV1ContextualUIntLiteral
        (GrammarV1UnsignedType "U8")
        (GrammarV1IntegerExpression "255")
        == Right (ScalarUIntLiteral 8 255)
    )
    "U8 maximum did not elaborate to exact Core scalar identity"
  case grammarV1ContextualUIntLiteral
      (GrammarV1UnsignedType "U8")
      (GrammarV1IntegerExpression "256") of
    Left (GrammarV1RuntimeUIntLiteralOutOfRange 8 256) -> Right ()
    other -> Left ("U8 out-of-range literal did not reject exactly: " <> show other)
  assert
    ( grammarV1ContextualUIntLiteral
        (GrammarV1UnsignedType "U32")
        (GrammarV1IntegerExpression "256")
        == Right (ScalarUIntLiteral 32 256)
    )
    "same unsuffixed literal did not receive its exact contextual U32 identity"
  case grammarV1ContextualUIntLiteral
      (GrammarV1UnsignedType "U8")
      (GrammarV1IntegerExpression "12x") of
    Left (GrammarV1RuntimeIntegerLiteralMalformed "12x") -> Right ()
    other -> Left ("malformed integer text was partially consumed: " <> show other)
  case grammarV1ContextualUIntLiteral
      GrammarV1BoolType
      (GrammarV1IntegerExpression "1") of
    Left (GrammarV1RuntimeUIntContextRequired GrammarV1BoolType) -> Right ()
    other -> Left ("integer literal acquired a non-UInt runtime context: " <> show other)
  case grammarV1ContextualUIntLiteral
      (GrammarV1UnsignedType "U0")
      (GrammarV1IntegerExpression "0") of
    Left (GrammarV1RuntimeUIntContextRequired (GrammarV1UnsignedType "U0")) -> Right ()
    other -> Left ("invalid UInt width became a runtime scalar context: " <> show other)
  case grammarV1ContextualUIntLiteral
      (GrammarV1UnsignedType "U8")
      (GrammarV1BoolExpression True) of
    Left (GrammarV1RuntimeIntegerLiteralRequired (GrammarV1BoolExpression True)) -> Right ()
    other -> Left ("non-integer expression entered UInt literal elaboration: " <> show other)

exactPlainUIntArithmetic :: Either String ()
exactPlainUIntArithmetic = do
  let site name = PlainUIntArithmeticSite
        { plainUIntArithmeticObligationId = ObligationId name
        , plainUIntArithmeticOrigin = "EXEC-008"
        , plainUIntArithmeticScope = "test"
        , plainUIntArithmeticRequiredPoint = "before arithmetic result use"
        }
      check operator left right result =
        checkPlainUIntArithmetic
          emptyCheckState
          operator
          8
          left
          right
          result

  assert
    ( check UIntAdd (RefUInt 8 10) (RefUInt 8 20) (RefUInt 8 30) (site "exec008.add")
        == Right (PlainUIntArithmeticEstablished (ScalarUIntLiteral 8 30))
    )
    "closed U8 addition did not preserve its exact mathematical result"
  assert
    ( check UIntSubtract (RefUInt 8 20) (RefUInt 8 7) (RefUInt 8 13) (site "exec008.sub")
        == Right (PlainUIntArithmeticEstablished (ScalarUIntLiteral 8 13))
    )
    "closed U8 subtraction did not preserve its exact mathematical result"
  assert
    ( check UIntMultiply (RefUInt 8 15) (RefUInt 8 15) (RefUInt 8 225) (site "exec008.mul")
        == Right (PlainUIntArithmeticEstablished (ScalarUIntLiteral 8 225))
    )
    "closed U8 multiplication did not preserve its exact mathematical result"

  case check UIntAdd (RefUInt 8 255) (RefUInt 8 1) (RefUInt 8 0) (site "exec008.overflow") of
    Left (UIntArithmeticKnownResultOutOfRange UIntAdd 8 255 1 256) -> Right ()
    other -> Left ("U8 addition overflow acquired target wrap behavior: " <> show other)
  case check UIntSubtract (RefUInt 8 0) (RefUInt 8 1) (RefUInt 8 255) (site "exec008.underflow") of
    Left (UIntArithmeticKnownResultOutOfRange UIntSubtract 8 0 1 (-1)) -> Right ()
    other -> Left ("U8 subtraction underflow acquired target wrap behavior: " <> show other)
  case check UIntMultiply (RefUInt 8 16) (RefUInt 8 16) (RefUInt 8 0) (site "exec008.mul-overflow") of
    Left (UIntArithmeticKnownResultOutOfRange UIntMultiply 8 16 16 256) -> Right ()
    other -> Left ("U8 multiplication overflow acquired target wrap behavior: " <> show other)
  case check UIntAdd (RefUInt 8 1) (RefUInt 8 2) (RefUInt 8 4) (site "exec008.wrong-result") of
    Left (UIntArithmeticKnownResultMismatch UIntAdd 8 1 2 3 4) -> Right ()
    other -> Left ("plain arithmetic accepted a target/result drift: " <> show other)

  let left = RefOpaque (SortUInt 8) "exec008.left"
      right = RefOpaque (SortUInt 8) "exec008.right"
      result = RefOpaque (SortUInt 8) "exec008.result"
      symbolicSite = site "exec008.symbolic"
  decision <- mapLeft show
    (check UIntAdd left right result symbolicSite)
  obligation <- case decision of
    PlainUIntArithmeticRequiresProof value -> Right value
    other -> Left ("symbolic plain arithmetic invented a result without proof: " <> show other)
  assert
    (obligationProposition obligation == plainUIntArithmeticProposition UIntAdd 8 left right result)
    "symbolic arithmetic obligation lost exact operator/width/operand/result identity"
  arithmeticContext0 <- mapLeft show
    (registerUIntArithmeticClaims emptyStaticContext)
  arithmeticContext <- mapLeft show
    (registerUIntArithmeticClaims arithmeticContext0)
  case resolveObligation
      arithmeticContext
      emptyCheckState
      emptyDischargePolicy
      obligation of
    Left (UnresolvedObligation actualId actualProposition) -> do
      assert (actualId == obligationId obligation)
        "ADR-025 unresolved arithmetic obligation lost its exact obligation id"
      assert (actualProposition == obligationProposition obligation)
        "ADR-025 unresolved arithmetic obligation lost its exact proposition"
    other -> Left
      ("plain symbolic arithmetic selected target behavior without proof/policy: " <> show other)

checkedUIntArithmeticOutcomes :: Either String ()
checkedUIntArithmeticOutcomes = do
  case checkCheckedUIntArithmetic
      UIntAdd 8 (ScalarUIntLiteral 8 10) (ScalarUIntLiteral 8 20) of
    Right (CheckedUIntArithmeticSucceeded success) -> do
      assert
        (checkedUIntArithmeticResult success == ScalarUIntLiteral 8 30)
        "checked U8 addition lost its exact mathematical success result"
      assert
        ( checkedUIntArithmeticExactProposition success
            == plainUIntArithmeticProposition
                UIntAdd 8 (RefUInt 8 10) (RefUInt 8 20) (RefUInt 8 30)
        )
        "checked U8 addition success lost its exact arithmetic evidence proposition"
    other -> Left ("checked U8 addition did not take the success branch: " <> show other)

  assert
    ( checkCheckedUIntArithmetic
        UIntAdd 8 (ScalarUIntLiteral 8 255) (ScalarUIntLiteral 8 1)
        == Right (CheckedUIntArithmeticNegative checkedUIntOverflowFailure)
    )
    "checked U8 addition overflow did not select its explicit typed-negative outcome"
  assert
    ( checkCheckedUIntArithmetic
        UIntSubtract 8 (ScalarUIntLiteral 8 0) (ScalarUIntLiteral 8 1)
        == Right (CheckedUIntArithmeticNegative checkedUIntUnderflowFailure)
    )
    "checked U8 subtraction underflow did not select its explicit typed-negative outcome"
  assert
    ( checkCheckedUIntArithmetic
        UIntMultiply 8 (ScalarUIntLiteral 8 16) (ScalarUIntLiteral 8 16)
        == Right (CheckedUIntArithmeticNegative checkedUIntOverflowFailure)
    )
    "checked U8 multiplication overflow did not select its explicit typed-negative outcome"
  case checkCheckedUIntArithmetic
      UIntAdd 8 (ScalarUIntLiteral 16 1) (ScalarUIntLiteral 8 1) of
    Left (CheckedUIntArithmeticOperandTypeMismatch _ (ScalarUIntLiteral 16 1) 8) -> Right ()
    other -> Left ("checked arithmetic coerced a wrong-width operand: " <> show other)

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
