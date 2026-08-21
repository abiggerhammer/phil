{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , emitObligation
  , emptyCheckState
  )
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , insertBinding
  , startSharedLoan
  )
import Phil.Core.Refinement (RefinementError (MissingEvidence))
import Phil.Core.Syntax
  ( Branch (..)
  , FrameId (FrameId)
  , GrammarId (GrammarId)
  , Mode (..)
  , Name (Name)
  , Obligation (Obligation)
  , ObligationId (ObligationId)
  , Outcome (Outcome)
  , PendingRecvSpec (PendingRecvSpec)
  , Proposition (Atom)
  , RefSort (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Core.Value
  ( EqualityBoundary (..)
  , ValueError (..)
  , ValueResult (..)
  , checkValue
  , compareTypes
  , definitionallyEqualTy
  , synthValue
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "literal values synthesize their intrinsic types" testLiteralSynthesis
    , test "UInt literals enforce width and mathematical range" testUIntBounds
    , test "Γ variable synthesis is reusable" testUnrestrictedVariable
    , test "A variable synthesis consumes the capability" testAffineVariable
    , test "Δ variable synthesis consumes the owner" testLinearVariable
    , test "borrowed owners cannot be consumed by value synthesis" testBorrowedOwner
    , test "PendingRecv cannot be consumed as an ordinary value" testPendingNotValue
    , test "ascription turns checking into synthesis" testAscription
    , test "ascription preserves structural mode of a variable use" testAscriptionPreservesMode
    , test "bad ascription is rejected" testBadAscription
    , test "checking accepts definitional equality" testCheckExact
    , test "dependent index mismatch requires explicit transport" testExplicitTransportBoundary
    , test "unrelated types are incompatible" testTypeMismatch
    , test "refined expected types require matching evidence" testRefinedExpected
    , test "refined ascriptions cannot erase proof obligations" testRefinedAscription
    , test "guarded recursive endpoint types compare equi-recursively" testRecursiveSessionEquality
    , test "choice label order does not affect session equality" testChoiceOrderEquality
    , test "different terminal outcomes are not definitionally equal" testSessionOutcomeMismatch
    , test "value checking preserves residual obligations" testObligationsPreserved
    , test "unknown variables are rejected" testUnknownVariable
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

var :: Text -> RefTerm
var = RefVar . name

versionsField :: RefTerm
versionsField = RefField (var "hello") "versions" (SortFiniteSeq (SortUInt 16))

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testLiteralSynthesis :: Either String ()
testLiteralSynthesis = do
  unitResult <- mapLeft show $ synthValue VUnit emptyCheckState
  boolResult <- mapLeft show $ synthValue (VBool True) emptyCheckState
  uintResult <- mapLeft show $ synthValue (VUInt 16 65535) emptyCheckState
  assert (valueResultType unitResult == TyUnit) "unit synthesized the wrong type"
  assert (valueResultType boolResult == TyBool) "bool synthesized the wrong type"
  assert (valueResultType uintResult == TyUInt 16) "UInt synthesized the wrong width"
  assert (valueResultState unitResult == emptyCheckState) "literal synthesis changed checker state"

testUIntBounds :: Either String ()
testUIntBounds = do
  case synthValue (VUInt 0 0) emptyCheckState of
    Left (InvalidUIntWidth 0) -> Right ()
    other -> Left ("zero-width UInt was not rejected: " ++ show other)
  case synthValue (VUInt 8 256) emptyCheckState of
    Left (UIntLiteralOutOfRange 8 256) -> Right ()
    other -> Left ("overflowing UInt literal was not rejected: " ++ show other)
  case synthValue (VUInt 8 (-1)) emptyCheckState of
    Left (UIntLiteralOutOfRange 8 (-1)) -> Right ()
    other -> Left ("negative UInt literal was not rejected: " ++ show other)

testUnrestrictedVariable :: Either String ()
testUnrestrictedVariable = do
  context <- mapLeft show $ insertBinding Unrestricted (name "policy") (TyOpaque "Policy") (resourceContext emptyCheckState)
  let state = emptyCheckState { resourceContext = context }
  first <- mapLeft show $ synthValue (VVar (name "policy")) state
  second <- mapLeft show $ synthValue (VVar (name "policy")) (valueResultState first)
  assert (valueResultMode first == Just Unrestricted) "Γ variable reported the wrong mode"
  assert (resourceContext (valueResultState second) == context) "Γ variable use changed the context"

testAffineVariable :: Either String ()
testAffineVariable = do
  context <- mapLeft show $ insertBinding Affine (name "cap") (TyOpaque "Capability") (resourceContext emptyCheckState)
  result <- mapLeft show $ synthValue (VVar (name "cap")) (emptyCheckState { resourceContext = context })
  assert (valueResultMode result == Just Affine) "affine variable reported the wrong mode"
  assert (Map.notMember (name "cap") (affineBindings (resourceContext (valueResultState result)))) "affine variable remained live after use"

testLinearVariable :: Either String ()
testLinearVariable = do
  context <- mapLeft show $ insertBinding Linear (name "payload") (TyBytes (RefNat 4096)) (resourceContext emptyCheckState)
  result <- mapLeft show $ synthValue (VVar (name "payload")) (emptyCheckState { resourceContext = context })
  assert (valueResultMode result == Just Linear) "linear variable reported the wrong mode"
  assert (Map.notMember (name "payload") (linearBindings (resourceContext (valueResultState result)))) "linear variable remained live after use"

testBorrowedOwner :: Either String ()
testBorrowedOwner = do
  context0 <- mapLeft show $ insertBinding Linear (name "payload") (TyBytes (RefNat 4096)) (resourceContext emptyCheckState)
  context1 <- mapLeft show $ startSharedLoan (name "payload") context0
  case synthValue (VVar (name "payload")) (emptyCheckState { resourceContext = context1 }) of
    Left (ValueResourceError (OwnerBorrowed owner)) ->
      assert (owner == name "payload") "borrow error named the wrong owner"
    other -> Left ("borrowed linear value was consumable: " ++ show other)

testPendingNotValue :: Either String ()
testPendingNotValue = do
  let pendingName = name "pending"
      pending = PendingRecvSpec
        (name "e0")
        (GrammarId "Hello")
        (FrameId "frame-1")
        (name "hello")
        (End (Outcome "success"))
      pendingTy = TyPendingRecv pending
  context <- mapLeft show $ insertBinding Linear pendingName pendingTy (resourceContext emptyCheckState)
  case synthValue (VVar pendingName) (emptyCheckState { resourceContext = context }) of
    Left (InternalResourceNotValue owner actualTy) ->
      assert (owner == pendingName && actualTy == pendingTy) "pending-resource rejection lost identity or type"
    other -> Left ("PendingRecv was consumable as an ordinary value: " ++ show other)

testAscription :: Either String ()
testAscription = do
  result <- mapLeft show $ synthValue (VAscribe (VUInt 16 7) (TyUInt 16)) emptyCheckState
  assert (valueResultType result == TyUInt 16) "ascription did not synthesize its annotation"

testAscriptionPreservesMode :: Either String ()
testAscriptionPreservesMode = do
  context <- mapLeft show $ insertBinding Linear (name "payload") (TyBytes (RefNat 4096)) (resourceContext emptyCheckState)
  result <- mapLeft show $ synthValue
    (VAscribe (VVar (name "payload")) (TyBytes (RefNat 4096)))
    (emptyCheckState { resourceContext = context })
  assert (valueResultMode result == Just Linear) "ascription erased the structural mode of its variable use"

testBadAscription :: Either String ()
testBadAscription =
  case synthValue (VAscribe (VBool True) (TyUInt 8)) emptyCheckState of
    Left (ValueTypeMismatch TyBool (TyUInt 8)) -> Right ()
    other -> Left ("bad ascription was not rejected: " ++ show other)

testCheckExact :: Either String ()
testCheckExact = do
  result <- mapLeft show $ checkValue (VUInt 32 42) (TyUInt 32) emptyCheckState
  assert (valueResultType result == TyUInt 32) "exact checking returned the wrong type"

testExplicitTransportBoundary :: Either String ()
testExplicitTransportBoundary = do
  let sourceTy = TyBytes (RefNat 4096)
      targetTy = TyBytes (RefToNat (RefField (var "begin") "length" (SortUInt 32)))
  context0 <- mapLeft show $ insertBinding Linear (name "payload") sourceTy (resourceContext emptyCheckState)
  context1 <- mapLeft show $ insertBinding Unrestricted (name "begin") (TyOpaque "Begin") context0
  case checkValue (VVar (name "payload")) targetTy (emptyCheckState { resourceContext = context1 }) of
    Left (ExplicitTransportRequired actual expected) ->
      assert (actual == sourceTy && expected == targetTy) "transport boundary reported the wrong types"
    other -> Left ("dependent mismatch did not demand explicit transport: " ++ show other)

testTypeMismatch :: Either String ()
testTypeMismatch =
  case checkValue (VBool False) (TyUInt 1) emptyCheckState of
    Left (ValueTypeMismatch TyBool (TyUInt 1)) -> Right ()
    other -> Left ("unrelated types were not rejected: " ++ show other)

testRefinedExpected :: Either String ()
testRefinedExpected = do
  context <- mapLeft show $ insertBinding Unrestricted (name "hello") (TyOpaque "Hello") (resourceContext emptyCheckState)
  let state = emptyCheckState { resourceContext = context }
      refined = TyRefined
        (name "v")
        (TyUInt 16)
        (Atom "member" [var "v", versionsField])
  case checkValue (VUInt 16 1) refined state of
    Left (ValueRefinementError (MissingEvidence required)) ->
      assert
        (required == Atom "member" [RefUInt 16 1, versionsField])
        "wrong instantiated refinement reported"
    other -> Left ("refined check bypassed evidence handling: " ++ show other)

testRefinedAscription :: Either String ()
testRefinedAscription = do
  context <- mapLeft show $ insertBinding Unrestricted (name "hello") (TyOpaque "Hello") (resourceContext emptyCheckState)
  let state = emptyCheckState { resourceContext = context }
      refined = TyRefined
        (name "v")
        (TyUInt 16)
        (Atom "member" [var "v", versionsField])
  case synthValue (VAscribe (VUInt 16 1) refined) state of
    Left (ValueRefinementError (MissingEvidence _)) -> Right ()
    other -> Left ("refined ascription bypassed evidence handling: " ++ show other)

testRecursiveSessionEquality :: Either String ()
testRecursiveSessionEquality = do
  let x = name "X"
      loop = Rec x (Receive (name "msg") TyBool (SessionVar x))
      unfolded = Receive (name "msg") TyBool loop
  assert (definitionallyEqualTy (TyEndpoint loop) (TyEndpoint unfolded)) "guarded recursive unfolding was not definitional"
  assert (compareTypes (TyEndpoint loop) (TyEndpoint unfolded) == DefinitionallyEqual) "recursive endpoints crossed the wrong equality boundary"

testChoiceOrderEquality :: Either String ()
testChoiceOrderEquality = do
  let branches =
        [ Branch "accepted" Nothing (End (Outcome "success"))
        , Branch "rejected" Nothing (End (Outcome "failure"))
        ]
      left = TyEndpoint (Offer branches)
      right = TyEndpoint (Offer (reverse branches))
  assert (definitionallyEqualTy left right) "choice branch ordering changed definitional equality"

testSessionOutcomeMismatch :: Either String ()
testSessionOutcomeMismatch =
  assert
    (compareTypes
      (TyEndpoint (End (Outcome "success")))
      (TyEndpoint (End (Outcome "failure")))
      == IncompatibleTypes)
    "distinct terminal outcomes compared equal"

testObligationsPreserved :: Either String ()
testObligationsPreserved = do
  let obligation = Obligation
        (ObligationId "value.test")
        (Atom "SomeClaim" [var "subject"])
        "ValueMain"
        "value-test"
        "after synthesis"
  state <- mapLeft show $ emitObligation obligation emptyCheckState
  result <- mapLeft show $ synthValue (VBool True) state
  assert
    (residualObligations (valueResultState result) == residualObligations state)
    "value synthesis changed residual obligations"

testUnknownVariable :: Either String ()
testUnknownVariable =
  case synthValue (VVar (name "missing")) emptyCheckState of
    Left (ValueResourceError (UnknownBinding missing)) ->
      assert (missing == name "missing") "unknown-variable error reported the wrong name"
    other -> Left ("unknown variable was not rejected: " ++ show other)

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
