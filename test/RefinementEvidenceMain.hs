{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , CheckerError (..)
  , emptyCheckState
  )
import Phil.Core.Context
  ( ResourceContext (..)
  , insertBinding
  )
import Phil.Core.Refinement
  ( EvidenceUse (..)
  , RefinementError (..)
  , ResidualSpec (..)
  , normalizeProposition
  , normalizeRefTerm
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (Name)
  , Obligation (..)
  , ObligationId (ObligationId)
  , Outcome (Outcome)
  , Proposition (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Core.Value
  ( EqualityBoundary (DefinitionallyEqual)
  , ValueError (..)
  , ValueResult (..)
  , checkValue
  , checkValueUsing
  , checkValueWithResidual
  , compareTypes
  , definitionallyEqualTy
  , synthValue
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "refinement terms normalize canonical UInt-to-Nat arithmetic" testTermNormalization
    , test "natural subtraction never silently truncates" testNaturalSubtraction
    , test "refined literal can discharge proposition definitionally" testDefinitionalRefinement
    , test "matching Proof evidence discharges a refined value" testMatchingProof
    , test "missing evidence rejects a refined value" testMissingEvidence
    , test "explicit using rejects mismatched evidence" testExplicitEvidenceMismatch
    , test "Validated evidence matches exact context and subject" testValidatedEvidence
    , test "stale validation context is rejected" testStaleValidationContext
    , test "validation evidence for the wrong subject is rejected" testWrongValidationSubject
    , test "opaque claims require explicit evidence" testOpaqueClaimRequiresEvidence
    , test "matching evidence may establish an opaque claim" testOpaqueClaimEvidence
    , test "explicit residualization emits stable obligation metadata" testResidualObligation
    , test "identical residualization is idempotent" testResidualIdempotent
    , test "conflicting residual obligation identity is rejected" testResidualConflict
    , test "definitionally false refinements cannot be residualized" testFalseCannotResidualize
    , test "linear transport consumes source and preserves proof" testLinearTransport
    , test "transport rejects a mismatched equality proof" testTransportWrongProof
    , test "transport rejects reversed equality without symmetry evidence" testTransportWrongDirection
    , test "transport rejects unrelated type families" testUnsupportedTransport
    , test "redundant transport is rejected" testTransportNotRequired
    , test "transport cannot erase a target refinement" testTransportTargetRefined
    , test "proof evidence remains reusable after explicit using" testProofReuse
    , test "affine proof bindings do not count as reusable evidence" testAffineProofNotEvidence
    , test "structured byte indices normalize for definitional equality" testByteIndexNormalization
    , test "Proof types compare after proposition normalization" testProofTypeNormalization
    , test "refinement binders compare alpha-equivalently" testRefinementAlphaEquality
    , test "dependent session binders compare alpha-equivalently" testSessionAlphaEquality
    , test "alpha-equivalence respects nested binder shadowing" testAlphaShadowing
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

var :: Text -> RefTerm
var = RefVar . name

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testTermNormalization :: Either String ()
testTermNormalization =
  assert
    (normalizeRefTerm (RefAdd (RefNat 0) (RefToNat (RefUInt 16 7))) == RefNat 7)
    "canonical UInt-to-Nat arithmetic did not normalize"

testNaturalSubtraction :: Either String ()
testNaturalSubtraction =
  assert
    (normalizeRefTerm (RefSub (RefNat 3) (RefNat 5)) == RefSub (RefNat 3) (RefNat 5))
    "Nat subtraction truncated without the required side condition"

testDefinitionalRefinement :: Either String ()
testDefinitionalRefinement = do
  let refined = TyRefined
        (name "v")
        (TyUInt 16)
        (Equal (RefToNat (var "v")) (RefNat 7))
  result <- mapLeft show $ checkValue (VUInt 16 7) refined emptyCheckState
  assert (valueResultType result == refined) "definitionally discharged refinement returned the wrong type"
  case valueResultEvidence result of
    [EvidenceByDefinition _] -> Right ()
    other -> Left ("definitional refinement recorded the wrong disposition: " ++ show other)

testMatchingProof :: Either String ()
testMatchingProof = do
  let required = Member (RefUInt 16 7) (RefField (var "hello") "versions")
      refined = TyRefined
        (name "v")
        (TyUInt 16)
        (Member (var "v") (RefField (var "hello") "versions"))
  state <- withUnrestricted (name "offered") (TyProof required) emptyCheckState
  result <- mapLeft show $ checkValue (VUInt 16 7) refined state
  assert
    (EvidenceByBinding (name "offered") (normalizeProposition required) `elem` valueResultEvidence result)
    "matching proof was not recorded as the refinement discharge"

testMissingEvidence :: Either String ()
testMissingEvidence = do
  let refined = TyRefined (name "v") (TyUInt 16) (Atom "Allowed" [var "v"])
  case checkValue (VUInt 16 1) refined emptyCheckState of
    Left (ValueRefinementError (MissingEvidence (Atom "Allowed" [RefUInt 16 1]))) -> Right ()
    other -> Left ("missing refinement evidence was not rejected: " ++ show other)

testExplicitEvidenceMismatch :: Either String ()
testExplicitEvidenceMismatch = do
  let expected = TyRefined (name "v") (TyUInt 16) (Atom "Allowed" [var "v"])
      wrongProof = TyProof (Atom "Allowed" [RefUInt 16 2])
  state <- withUnrestricted (name "proof") wrongProof emptyCheckState
  case checkValueUsing (name "proof") (VUInt 16 1) expected state of
    Left (ValueRefinementError (EvidenceDoesNotMatch proof _ _)) ->
      assert (proof == name "proof") "wrong evidence binding reported"
    other -> Left ("explicit mismatched evidence was accepted: " ++ show other)

testValidatedEvidence :: Either String ()
testValidatedEvidence = do
  state0 <- withUnrestricted (name "begin") (TyOpaque "Begin") emptyCheckState
  state1 <- withUnrestricted
    (name "beginPolicy")
    (TyValidated "BeginPolicy" (name "κ1") (name "begin"))
    state0
  let refined = TyRefined
        (name "x")
        (TyOpaque "Begin")
        (Atom "BeginPolicy" [var "κ1", var "x"])
  result <- mapLeft show $ checkValue (VVar (name "begin")) refined state1
  assert
    (EvidenceByBinding
      (name "beginPolicy")
      (Atom "BeginPolicy" [var "κ1", var "begin"])
      `elem` valueResultEvidence result)
    "Validated evidence did not discharge the exact context/subject proposition"

testStaleValidationContext :: Either String ()
testStaleValidationContext = do
  state0 <- withUnrestricted (name "begin") (TyOpaque "Begin") emptyCheckState
  state1 <- withUnrestricted
    (name "stale")
    (TyValidated "BeginPolicy" (name "κ1") (name "begin"))
    state0
  let refined = TyRefined
        (name "x")
        (TyOpaque "Begin")
        (Atom "BeginPolicy" [var "κ2", var "x"])
  case checkValue (VVar (name "begin")) refined state1 of
    Left (ValueRefinementError (MissingEvidence required)) ->
      assert
        (required == Atom "BeginPolicy" [var "κ2", var "begin"])
        "stale-context rejection reported the wrong proposition"
    other -> Left ("stale validation context was accepted: " ++ show other)

testWrongValidationSubject :: Either String ()
testWrongValidationSubject = do
  state0 <- withUnrestricted (name "begin2") (TyOpaque "Begin") emptyCheckState
  state1 <- withUnrestricted
    (name "wrongSubject")
    (TyValidated "BeginPolicy" (name "κ1") (name "begin1"))
    state0
  let refined = TyRefined
        (name "x")
        (TyOpaque "Begin")
        (Atom "BeginPolicy" [var "κ1", var "x"])
  case checkValue (VVar (name "begin2")) refined state1 of
    Left (ValueRefinementError (MissingEvidence required)) ->
      assert
        (required == Atom "BeginPolicy" [var "κ1", var "begin2"])
        "wrong-subject rejection reported the wrong proposition"
    other -> Left ("validation evidence for another subject was accepted: " ++ show other)

testOpaqueClaimRequiresEvidence :: Either String ()
testOpaqueClaimRequiresEvidence = do
  state <- withUnrestricted (name "payload") (TyOpaque "Payload") emptyCheckState
  let refined = TyRefined
        (name "x")
        (TyOpaque "Payload")
        (Atom "DigestMatches" [var "begin", var "x"])
  case checkValue (VVar (name "payload")) refined state of
    Left (ValueRefinementError (MissingEvidence required)) ->
      assert
        (required == Atom "DigestMatches" [var "begin", var "payload"])
        "opaque-claim rejection lost the subject identity"
    other -> Left ("opaque claim was established without evidence: " ++ show other)

testOpaqueClaimEvidence :: Either String ()
testOpaqueClaimEvidence = do
  state0 <- withUnrestricted (name "payload") (TyOpaque "Payload") emptyCheckState
  state1 <- withUnrestricted
    (name "digestEvidence")
    (TyProof (Atom "DigestMatches" [var "begin", var "payload"]))
    state0
  let refined = TyRefined
        (name "x")
        (TyOpaque "Payload")
        (Atom "DigestMatches" [var "begin", var "x"])
  _ <- mapLeft show $ checkValue (VVar (name "payload")) refined state1
  Right ()

testResidualObligation :: Either String ()
testResidualObligation = do
  let refined = TyRefined (name "v") (TyUInt 16) (Atom "NeedsRuntime" [var "v"])
      spec = ResidualSpec
        (ObligationId "upload.value.runtime")
        "server.phil:value"
        "upload-server"
        "before store"
  result <- mapLeft show $ checkValueWithResidual spec (VUInt 16 5) refined emptyCheckState
  case Map.lookup (ObligationId "upload.value.runtime") (residualObligations (valueResultState result)) of
    Just obligation -> do
      assert
        (obligationProposition obligation == Atom "NeedsRuntime" [RefUInt 16 5])
        "residual obligation proposition was not instantiated"
      assert (obligationOrigin obligation == "server.phil:value") "residual origin was lost"
      assert (obligationScope obligation == "upload-server") "residual scope was lost"
      assert (obligationRequiredPoint obligation == "before store") "required point was lost"
    Nothing -> Left "explicit residualization did not emit its stable obligation"

testResidualIdempotent :: Either String ()
testResidualIdempotent = do
  let refined = TyRefined (name "v") (TyUInt 16) (Atom "NeedsRuntime" [var "v"])
      spec = ResidualSpec (ObligationId "same.id") "origin" "scope" "point"
  first <- mapLeft show $ checkValueWithResidual spec (VUInt 16 5) refined emptyCheckState
  second <- mapLeft show $ checkValueWithResidual spec (VUInt 16 5) refined (valueResultState first)
  assert
    (Map.size (residualObligations (valueResultState second)) == 1)
    "identical residualization duplicated a stable obligation"

testResidualConflict :: Either String ()
testResidualConflict = do
  let firstTy = TyRefined (name "v") (TyUInt 16) (Atom "First" [var "v"])
      secondTy = TyRefined (name "v") (TyUInt 16) (Atom "Second" [var "v"])
      spec = ResidualSpec (ObligationId "conflict.id") "origin" "scope" "point"
  first <- mapLeft show $ checkValueWithResidual spec (VUInt 16 5) firstTy emptyCheckState
  case checkValueWithResidual spec (VUInt 16 5) secondTy (valueResultState first) of
    Left (ValueRefinementError (ResidualObligationError (ConflictingObligationId _ _))) -> Right ()
    other -> Left ("conflicting residual identity was not rejected: " ++ show other)

testFalseCannotResidualize :: Either String ()
testFalseCannotResidualize = do
  let refined = TyRefined
        (name "v")
        (TyUInt 16)
        (Equal (RefToNat (var "v")) (RefNat 2))
      spec = ResidualSpec (ObligationId "false.id") "origin" "scope" "point"
  case checkValueWithResidual spec (VUInt 16 1) refined emptyCheckState of
    Left (ValueRefinementError (StaticallyFalse _)) -> Right ()
    other -> Left ("definitionally false proposition was residualized: " ++ show other)

testLinearTransport :: Either String ()
testLinearTransport = do
  let sourceTy = TyBytes (RefNat 4096)
      targetIndex = RefToNat (RefField (var "begin") "length")
      targetTy = TyBytes targetIndex
      proofTy = TyProof (Equal (RefNat 4096) targetIndex)
  context0 <- mapLeft show $ insertBinding Linear (name "payload") sourceTy (resourceContext emptyCheckState)
  context1 <- mapLeft show $ insertBinding Unrestricted (name "lengthEq") proofTy context0
  let state = emptyCheckState { resourceContext = context1 }
  result <- mapLeft show $ synthValue (VTransport (VVar (name "payload")) (name "lengthEq") targetTy) state
  assert (valueResultType result == targetTy) "transport produced the wrong target type"
  assert (valueResultMode result == Just Linear) "transport lost linear ownership mode"
  let residual = resourceContext (valueResultState result)
  assert (Map.notMember (name "payload") (linearBindings residual)) "transport duplicated the source linear owner"
  assert (Map.member (name "lengthEq") (unrestrictedBindings residual)) "transport consumed reusable equality evidence"

testTransportWrongProof :: Either String ()
testTransportWrongProof = do
  let sourceTy = TyBytes (RefNat 4096)
      targetTy = TyBytes (var "n")
      wrong = TyProof (Equal (RefNat 4096) (var "m"))
  state0 <- withLinear (name "payload") sourceTy emptyCheckState
  state1 <- withUnrestricted (name "wrong") wrong state0
  case synthValue (VTransport (VVar (name "payload")) (name "wrong") targetTy) state1 of
    Left (ValueRefinementError (EvidenceDoesNotMatch _ _ _)) -> Right ()
    other -> Left ("transport accepted a mismatched proof: " ++ show other)

testTransportWrongDirection :: Either String ()
testTransportWrongDirection = do
  let sourceTy = TyBytes (RefNat 4096)
      targetTy = TyBytes (var "n")
      reversed = TyProof (Equal (var "n") (RefNat 4096))
  state0 <- withLinear (name "payload") sourceTy emptyCheckState
  state1 <- withUnrestricted (name "reversed") reversed state0
  case synthValue (VTransport (VVar (name "payload")) (name "reversed") targetTy) state1 of
    Left (ValueRefinementError (EvidenceDoesNotMatch _ _ _)) -> Right ()
    other -> Left ("transport silently used equality symmetry: " ++ show other)

testUnsupportedTransport :: Either String ()
testUnsupportedTransport =
  case synthValue (VTransport (VBool True) (name "proof") (TyUInt 1)) emptyCheckState of
    Left (UnsupportedTransport TyBool (TyUInt 1)) -> Right ()
    other -> Left ("unrelated transport was not rejected: " ++ show other)

testTransportNotRequired :: Either String ()
testTransportNotRequired = do
  state <- withUnrestricted (name "proof") (TyProof Truth) emptyCheckState
  case synthValue (VTransport (VUInt 16 1) (name "proof") (TyUInt 16)) state of
    Left (TransportNotRequired (TyUInt 16)) -> Right ()
    other -> Left ("redundant transport was not rejected: " ++ show other)

testTransportTargetRefined :: Either String ()
testTransportTargetRefined = do
  let target = TyRefined (name "v") (TyUInt 16) (Atom "Allowed" [var "v"])
  case synthValue (VTransport (VUInt 16 1) (name "proof") target) emptyCheckState of
    Left (TransportTargetRefined actual) -> assert (actual == target) "wrong refined target reported"
    other -> Left ("transport erased a target refinement: " ++ show other)

testProofReuse :: Either String ()
testProofReuse = do
  let proofTy = TyProof (Atom "Allowed" [RefUInt 16 1])
      refined = TyRefined (name "v") (TyUInt 16) (Atom "Allowed" [var "v"])
  state <- withUnrestricted (name "proof") proofTy emptyCheckState
  first <- mapLeft show $ checkValueUsing (name "proof") (VUInt 16 1) refined state
  second <- mapLeft show $ checkValueUsing (name "proof") (VUInt 16 1) refined (valueResultState first)
  assert
    (Map.member (name "proof") (unrestrictedBindings (resourceContext (valueResultState second))))
    "using proof evidence consumed it from Γ"

testAffineProofNotEvidence :: Either String ()
testAffineProofNotEvidence = do
  let required = Atom "Allowed" [RefUInt 16 1]
      refined = TyRefined (name "v") (TyUInt 16) (Atom "Allowed" [var "v"])
  state <- withAffine (name "proof") (TyProof required) emptyCheckState
  case checkValue (VUInt 16 1) refined state of
    Left (ValueRefinementError (MissingEvidence actual)) ->
      assert (actual == required) "wrong missing proposition reported"
    other -> Left ("affine proof was treated as reusable evidence: " ++ show other)

testByteIndexNormalization :: Either String ()
testByteIndexNormalization = do
  let left = TyBytes (RefToNat (RefUInt 16 5))
      right = TyBytes (RefNat 5)
  assert (definitionallyEqualTy left right) "normalized byte indices were not definitionally equal"
  assert (compareTypes left right == DefinitionallyEqual) "normalized byte indices crossed the wrong equality boundary"

testProofTypeNormalization :: Either String ()
testProofTypeNormalization = do
  let left = TyProof (Equal (RefToNat (RefUInt 16 7)) (RefNat 7))
      right = TyProof Truth
  assert (definitionallyEqualTy left right) "proof propositions did not normalize for type equality"

testRefinementAlphaEquality :: Either String ()
testRefinementAlphaEquality = do
  let left = TyRefined
        (name "x")
        (TyUInt 16)
        (Equal (RefToNat (var "x")) (RefNat 7))
      right = TyRefined
        (name "y")
        (TyUInt 16)
        (Equal (RefToNat (var "y")) (RefNat 7))
  assert (definitionallyEqualTy left right) "alpha-renamed refinement binders compared unequal"

testSessionAlphaEquality :: Either String ()
testSessionAlphaEquality = do
  let success = Outcome "success"
      left = TyEndpoint
        (Receive
          (name "n")
          (TyUInt 16)
          (Send (name "body") (TyBytes (RefToNat (var "n"))) (End success)))
      right = TyEndpoint
        (Receive
          (name "length")
          (TyUInt 16)
          (Send (name "body") (TyBytes (RefToNat (var "length"))) (End success)))
  assert (definitionallyEqualTy left right) "alpha-renamed dependent session binders compared unequal"

testAlphaShadowing :: Either String ()
testAlphaShadowing = do
  let success = Outcome "success"
      left = TyEndpoint
        (Receive
          (name "outer")
          (TyUInt 16)
          (Receive
            (name "inner")
            (TyUInt 16)
            (Send (name "body") (TyBytes (RefToNat (var "inner"))) (End success))))
      right = TyEndpoint
        (Receive
          (name "x")
          (TyUInt 16)
          (Receive
            (name "x")
            (TyUInt 16)
            (Send (name "body") (TyBytes (RefToNat (var "x"))) (End success))))
  assert (definitionallyEqualTy left right) "nested shadowing broke capture-safe alpha-equivalence"

withUnrestricted :: Name -> Ty -> CheckState -> Either String CheckState
withUnrestricted binding ty state = do
  context <- mapLeft show $ insertBinding Unrestricted binding ty (resourceContext state)
  Right (state { resourceContext = context })

withAffine :: Name -> Ty -> CheckState -> Either String CheckState
withAffine binding ty state = do
  context <- mapLeft show $ insertBinding Affine binding ty (resourceContext state)
  Right (state { resourceContext = context })

withLinear :: Name -> Ty -> CheckState -> Either String CheckState
withLinear binding ty state = do
  context <- mapLeft show $ insertBinding Linear binding ty (resourceContext state)
  Right (state { resourceContext = context })

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
