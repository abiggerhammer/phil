{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Checker (CheckState (..), emptyCheckState, emitObligation)
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , insertBinding
  , startSharedLoan
  )
import Phil.Core.Refinement
  ( RefinementError (..)
  )
import Phil.Core.SortCheck
  ( SortError (..)
  , checkTypeSorts
  , sortOfRefTerm
  )
import Phil.Core.Syntax
import Phil.Core.Value
  ( ValueError (..)
  , ValueResult (..)
  , checkValue
  , synthValue
  )
import System.Exit (exitFailure)

type Check = Either String ()

end :: Session
end = End (Outcome "success")

endpointName, keeperName :: Name
endpointName = Name "endpoint"
keeperName = Name "unrelated"

recv, send, offer, later :: Ty -> Ty
recv payload =
  TyEndpoint (Receive (Name "message") payload end)
send payload =
  TyEndpoint (Send (Name "message") payload end)
offer payload =
  TyEndpoint
    (Offer [Branch "data" (Just (Name "message", payload)) end])
later payload =
  TyEndpoint
    (Receive
      (Name "flag")
      TyBool
      (Send (Name "message") payload end))

badIndex :: RefTerm
badIndex = RefScale 0 (RefBool True)

badPredicate :: Proposition
badPredicate = Equal badIndex (RefNat 0)

badSort :: SortError
badSort = ExpectedNatOperand (RefBool True) SortBool

main :: IO ()
main = do
  results <- sequence
    [ test "S01 receive payload rejects hidden Bool-as-Nat"
        (sortRegression checkValue
          (recv (TyBytes (RefNat 0)))
          (recv (TyBytes badIndex))
          badSort)
    , test "S02 ascription rejects hidden Bool-as-Nat"
        (sortRegression ascribe
          (recv (TyBytes (RefNat 0)))
          (recv (TyBytes badIndex))
          badSort)
    , test "S03 send payload rejects hidden Bool-as-Nat"
        (sortRegression checkValue
          (send (TyBytes (RefNat 0)))
          (send (TyBytes badIndex))
          badSort)
    , test "S04 branch payload rejects hidden Bool-as-Nat"
        (sortRegression checkValue
          (offer (TyBytes (RefNat 0)))
          (offer (TyBytes badIndex))
          badSort)
    , test "S05 later continuation payload rejects hidden Bool-as-Nat"
        (sortRegression checkValue
          (later (TyBytes (RefNat 0)))
          (later (TyBytes badIndex))
          badSort)
    , test "S06 nested refinement predicate is sorted"
        (sortRegression checkValue
          (recv (TyRefined (Name "v") TyBool Truth))
          (recv (TyRefined (Name "v") TyBool badPredicate))
          badSort)
    , test "S07 hidden out-of-range UInt literal rejects"
        (sortRegression checkValue
          (recv (TyBytes (RefNat 256)))
          (recv (TyBytes (RefToNat (RefUInt 8 256))))
          (InvalidUIntLiteral 8 256))
    , test "S08 Proof payload predicate is sorted"
        (sortRegression checkValue
          (recv (TyProof Truth))
          (recv (TyProof badPredicate))
          badSort)
    , test "C01 direct malformed term remains rejected"
        (assert
          (sortOfRefTerm emptyCheckState badIndex == Left badSort)
          "direct term sorting accepted Bool scale")
    , test "C02 direct malformed Bytes remains rejected"
        directBytesReject
    , test "C03 direct malformed Proof remains rejected"
        directProofReject
    , test "C04 valid normalizing index remains accepted"
        (acceptedPair
          (recv (TyBytes (RefNat 0)))
          (recv (TyBytes (RefScale 0 (RefNat 4)))))
    , test "C05 valid dependent continuation remains accepted"
        (acceptedPair (dependent "count") (dependent "count"))
    , test "C06 alpha-renamed dependent continuation remains accepted"
        (acceptedPair (dependent "count") (dependent "renamed"))
    , test "C07 guarded recursion remains finite and accepted"
        (acceptedPair
          (TyEndpoint loop)
          (TyEndpoint (Receive (Name "flag") TyBool loop)))
    , test "C08 real payload mismatch remains rejected"
        (mismatchedPair (recv (TyUInt 8)) (recv (TyUInt 16)))
    , test "C09 outcome mismatch remains rejected"
        (mismatchedPair
          (recv TyBool)
          (TyEndpoint
            (Receive
              (Name "message")
              TyBool
              (End (Outcome "failure")))))
    , test "C10 borrowed endpoint remains rejected"
        borrowedReject
    , test "C11 unknown endpoint remains rejected"
        unknownReject
    , test "C12 well-sorted uninhabited refinement remains accepted"
        (assert
          (checkTypeSorts
            emptyCheckState
            (recv (TyRefined (Name "v") TyBool Falsehood)) == Right ())
          "well-sorted uninhabited payload was treated as malformed")
    ]
  if and results then pure () else exitFailure

test :: String -> Check -> IO Bool
test label result =
  case result of
    Right () ->
      putStrLn ("PASS: PHIL-AUD-SESSION-TYPE-SORT-001 " <> label)
        >> pure True
    Left detail ->
      putStrLn
        ("FAIL: PHIL-AUD-SESSION-TYPE-SORT-001 "
          <> label <> " -- " <> detail)
        >> pure False

seed :: Ty -> Either String CheckState
seed ty = do
  context0 <- mapLeft show $
    insertBinding
      Unrestricted
      keeperName
      TyBool
      (resourceContext emptyCheckState)
  context1 <- mapLeft show $
    insertBinding Linear endpointName ty context0
  mapLeft show $
    emitObligation
      (Obligation
        (ObligationId "already.pending")
        Truth
        "origin"
        "scope"
        "point")
      (emptyCheckState { resourceContext = context1 })

sortRegression
  :: (Value -> Ty -> CheckState -> Either ValueError ValueResult)
  -> Ty
  -> Ty
  -> SortError
  -> Check
sortRegression check good bad expectedError = do
  state <- seed good
  case check (VVar endpointName) bad state of
    Left (ValueRefinementError (RefinementSortError actualError))
      | actualError == expectedError -> Right ()
      | otherwise ->
          Left ("wrong sort rejection: " <> show actualError)
    other ->
      Left
        ("ill-sorted annotation was not rejected at the sort boundary: "
          <> show other)

ascribe
  :: Value
  -> Ty
  -> CheckState
  -> Either ValueError ValueResult
ascribe value ty =
  synthValue (VAscribe value ty)

acceptedPair :: Ty -> Ty -> Check
acceptedPair good expected = do
  state <- seed good
  case checkValue (VVar endpointName) expected state of
    Left err -> Left ("unexpected rejection: " <> show err)
    Right result -> do
      assert
        (valueResultType result == expected)
        "wrong returned annotation"
      assert
        (valueResultMode result == Just Linear)
        "wrong ownership mode"
      assert
        (valueResultTerm result == Just (RefVar endpointName))
        "changed subject term"
      assert
        (null (valueResultEvidence result))
        "unexpected evidence"
      let context = resourceContext state
          expectedState = state
            { resourceContext =
                context
                  { linearBindings =
                      Map.delete endpointName (linearBindings context)
                  }
            }
      assert
        (valueResultState result == expectedState)
        "ownership, unrelated binding, or residual inventory changed"

mismatchedPair :: Ty -> Ty -> Check
mismatchedPair good expected = do
  state <- seed good
  case checkValue (VVar endpointName) expected state of
    Left (ValueTypeMismatch actual bad)
      | actual == good && bad == expected -> Right ()
    other -> Left ("wrong mismatch result: " <> show other)

dependent :: String -> Ty
dependent spelling =
  let binder = Name (fromString spelling)
  in TyEndpoint
      (Receive
        binder
        (TyUInt 8)
        (Send
          (Name "payload")
          (TyBytes (RefToNat (RefVar binder)))
          end))

loop :: Session
loop =
  Rec
    (Name "X")
    (Receive
      (Name "flag")
      TyBool
      (SessionVar (Name "X")))

directBytesReject :: Check
directBytesReject = do
  state <- seed (TyBytes (RefNat 0))
  case checkValue
      (VVar endpointName)
      (TyBytes badIndex)
      state of
    Left
      (ValueRefinementError
        (RefinementSortError
          (ExpectedNatOperand (RefBool True) SortBool))) ->
            Right ()
    other -> Left (show other)

directProofReject :: Check
directProofReject = do
  context <- mapLeft show $
    insertBinding
      Unrestricted
      (Name "proof")
      (TyProof Truth)
      (resourceContext emptyCheckState)
  case checkValue
      (VVar (Name "proof"))
      (TyProof badPredicate)
      (emptyCheckState { resourceContext = context }) of
    Left
      (ValueRefinementError
        (RefinementSortError
          (ExpectedNatOperand (RefBool True) SortBool))) ->
            Right ()
    other -> Left (show other)

borrowedReject :: Check
borrowedReject = do
  state <- seed (recv TyBool)
  context <- mapLeft show $
    startSharedLoan endpointName (resourceContext state)
  case checkValue
      (VVar endpointName)
      (recv TyBool)
      (state { resourceContext = context }) of
    Left (ValueResourceError (OwnerBorrowed actual))
      | actual == endpointName -> Right ()
    other -> Left (show other)

unknownReject :: Check
unknownReject =
  case checkValue
      (VVar endpointName)
      (recv TyBool)
      emptyCheckState of
    Left (ValueResourceError (UnknownBinding actual))
      | actual == endpointName -> Right ()
    other -> Left (show other)

fromString :: String -> Data.Text.Text
fromString = Data.Text.pack

assert :: Bool -> String -> Check
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
