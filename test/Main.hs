{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , CheckerError (..)
  , completeComponent
  , emitObligation
  , emptyCheckState
  )
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , consumeAffine
  , consumeLinear
  , emptyContext
  , endSharedLoan
  , ensureComplete
  , insertBinding
  , joinContinuing
  , startSharedLoan
  , useUnrestricted
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (Name)
  , Obligation (Obligation)
  , ObligationId (ObligationId)
  , Proposition (Atom)
  , Ty (TyOpaque)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Γ values are reusable" testUnrestrictedReuse
    , test "A values are consumable at most once" testAffineAtMostOnce
    , test "shared loan blocks owner consumption" testSharedLoanBlocksConsumption
    , test "Δ mismatch rejects branch join" testLinearBranchMismatch
    , test "A join conservatively forgets consumed capability" testAffineJoinForgets
    , test "complete component rejects leftover Δ" testLinearResidueRejected
    , test "obligation IDs reject conflicting reuse" testObligationIdConflict
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

nty :: Text -> Ty
nty = TyOpaque

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testUnrestrictedReuse :: Either String ()
testUnrestrictedReuse = do
  context0 <- mapLeft show $ insertBinding Unrestricted (name "policy") (nty "Policy") emptyContext
  (_, context1) <- mapLeft show $ useUnrestricted (name "policy") context0
  (_, context2) <- mapLeft show $ useUnrestricted (name "policy") context1
  assert (context2 == context0) "unrestricted use changed Γ"

testAffineAtMostOnce :: Either String ()
testAffineAtMostOnce = do
  context0 <- mapLeft show $ insertBinding Affine (name "cap") (nty "Capability") emptyContext
  (_, context1) <- mapLeft show $ consumeAffine (name "cap") context0
  case consumeAffine (name "cap") context1 of
    Left (UnknownBinding _) -> Right ()
    other -> Left ("second affine consumption was not rejected as expected: " ++ show other)

testSharedLoanBlocksConsumption :: Either String ()
testSharedLoanBlocksConsumption = do
  context0 <- mapLeft show $ insertBinding Linear (name "payload") (nty "Bytes[4096]") emptyContext
  context1 <- mapLeft show $ startSharedLoan (name "payload") context0
  case consumeLinear (name "payload") context1 of
    Left (OwnerBorrowed _) -> pure ()
    other -> Left ("borrowed owner consumption was not rejected: " ++ show other)
  context2 <- mapLeft show $ endSharedLoan (name "payload") context1
  (_, context3) <- mapLeft show $ consumeLinear (name "payload") context2
  mapLeft show $ ensureComplete context3

testLinearBranchMismatch :: Either String ()
testLinearBranchMismatch = do
  incoming <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  (_, consumed) <- mapLeft show $ consumeLinear (name "endpoint") incoming
  case joinContinuing [incoming, consumed] of
    Left (LinearBranchMismatch _ _) -> Right ()
    other -> Left ("linear branch mismatch was not rejected: " ++ show other)

testAffineJoinForgets :: Either String ()
testAffineJoinForgets = do
  incoming <- mapLeft show $ insertBinding Affine (name "cap") (nty "Capability") emptyContext
  (_, consumed) <- mapLeft show $ consumeAffine (name "cap") incoming
  joined <- mapLeft show $ joinContinuing [incoming, consumed]
  assert (Map.null (affineBindings joined)) "affine capability survived a join where one branch consumed it"

testLinearResidueRejected :: Either String ()
testLinearResidueRejected = do
  context <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  let state = emptyCheckState { resourceContext = context }
  case completeComponent state of
    Left (ResourceError (UnconsumedLinearResources _)) -> Right ()
    other -> Left ("leftover linear resource was not rejected: " ++ show other)

testObligationIdConflict :: Either String ()
testObligationIdConflict = do
  let first = Obligation
        (ObligationId "upload.begin.policy")
        (Atom "BeginPolicy" ["κ1", "begin"])
        "server.phil:begin"
        "before Accept"
      conflicting = Obligation
        (ObligationId "upload.begin.policy")
        (Atom "BeginPolicy" ["κ2", "begin"])
        "server.phil:begin"
        "before Accept"
  state1 <- mapLeft show $ emitObligation first emptyCheckState
  _ <- mapLeft show $ emitObligation first state1
  case emitObligation conflicting state1 of
    Left (ConflictingObligationId _ _) -> Right ()
    other -> Left ("conflicting obligation identity was not rejected: " ++ show other)

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
