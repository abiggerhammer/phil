{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , insertBinding
  , startSharedLoan
  )
import Phil.Core.Refinement
  ( EvidenceUse (..)
  , RefinementError (..)
  , ResidualSpec (..)
  )
import Phil.Core.SortCheck (SortError (..))
import Phil.Core.Syntax
  ( Mode (..)
  , Name (Name)
  , Obligation (..)
  , ObligationId (ObligationId)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Core.Value
  ( ValueError (..)
  , ValueResult (..)
  , checkValue
  , checkValueUsing
  , checkValueWithResidual
  , synthValue
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "R01 linear subject remains logically visible after consumption" testLinearSubjectVisible
    , test "R02 affine subject remains logically visible after consumption" testAffineSubjectVisible
    , test "R03 explicit evidence may mention the consumed subject" testExplicitEvidenceSubject
    , test "R04 carried evidence may mention the consumed subject" testCarriedEvidenceSubject
    , test "R05 ascription preserves consumed-subject refinement checking" testAscriptionSubject
    , test "R06 residual refinement keeps obligation but not ownership" testResidualSubject
    , test "C01 subject-independent linear refinement still consumes once" testSubjectIndependentLinear
    , test "C02 actively borrowed linear subject still rejects consumption" testBorrowedSubjectRejects
    , test "C03 unrestricted refinement subject remains live" testUnrestrictedSubject
    , test "C04 malformed subject predicate still fails sort checking" testMalformedPredicateRejects
    , test "C05 missing evidence reports evidence absence, not subject absence" testMissingEvidenceNotMissingSubject
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

payload :: Name
payload = name "payload"

proof :: Name
proof = name "proof"

bytes7 :: Ty
bytes7 = TyBytes (RefNat 7)

reflexiveLengthType :: Ty
reflexiveLengthType =
  TyRefined
    (name "s")
    bytes7
    (Equal (RefLen (RefVar (name "s"))) (RefLen (RefVar (name "s"))))

exactLengthProposition :: RefTerm -> Proposition
exactLengthProposition subject = Equal (RefLen subject) (RefNat 7)

exactLengthType :: Ty
exactLengthType =
  TyRefined
    (name "s")
    bytes7
    (exactLengthProposition (RefVar (name "s")))

opaqueRequirementType :: Ty
opaqueRequirementType =
  TyRefined
    (name "s")
    bytes7
    (Atom "NeedsAudit" [RefVar (name "s")])

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testLinearSubjectVisible :: Either String ()
testLinearSubjectVisible = do
  state <- withBinding Linear payload bytes7 emptyCheckState
  result <- mapLeft show $ checkValue (VVar payload) reflexiveLengthType state
  assert (ownerAbsent payload result) "linear owner survived refinement checking"
  assert
    (any isDefinitionalEvidence (valueResultEvidence result))
    "reflexive subject predicate did not discharge definitionally"

testAffineSubjectVisible :: Either String ()
testAffineSubjectVisible = do
  state <- withBinding Affine payload bytes7 emptyCheckState
  result <- mapLeft show $ checkValue (VVar payload) reflexiveLengthType state
  assert (ownerAbsent payload result) "affine owner survived refinement checking"

testExplicitEvidenceSubject :: Either String ()
testExplicitEvidenceSubject = do
  let required = exactLengthProposition (RefVar payload)
  state0 <- withBinding Linear payload bytes7 emptyCheckState
  state <- withBinding Unrestricted proof (TyProof required) state0
  result <- mapLeft show $ checkValueUsing proof (VVar payload) exactLengthType state
  assert (ownerAbsent payload result) "explicit evidence restored the linear owner"
  assert
    (Map.member proof (unrestrictedBindings (resourceContext (valueResultState result))))
    "explicit proof evidence was consumed"
  assert
    (EvidenceByBinding proof required `elem` valueResultEvidence result)
    "explicit proof evidence was not recorded"

testCarriedEvidenceSubject :: Either String ()
testCarriedEvidenceSubject = do
  let required = exactLengthProposition (RefVar payload)
  state <- withBinding Linear payload exactLengthType emptyCheckState
  result <- mapLeft show $ checkValue (VVar payload) exactLengthType state
  assert (ownerAbsent payload result) "carried evidence restored the linear owner"
  assert
    (EvidenceByBinding payload required `elem` valueResultEvidence result)
    "subject-bound carried evidence was not retained"

testAscriptionSubject :: Either String ()
testAscriptionSubject = do
  state <- withBinding Linear payload bytes7 emptyCheckState
  result <- mapLeft show $ synthValue (VAscribe (VVar payload) reflexiveLengthType) state
  assert (ownerAbsent payload result) "ascription restored the linear owner"
  assert (valueResultType result == reflexiveLengthType) "ascription returned the wrong type"

testResidualSubject :: Either String ()
testResidualSubject = do
  state <- withBinding Linear payload bytes7 emptyCheckState
  let spec = ResidualSpec
        (ObligationId "audit.payload")
        "audit"
        "component"
        "after payload consumption"
      required = Atom "NeedsAudit" [RefVar payload]
  result <- mapLeft show $ checkValueWithResidual spec (VVar payload) opaqueRequirementType state
  assert (ownerAbsent payload result) "residualization restored the linear owner"
  case Map.lookup (ObligationId "audit.payload") (residualObligations (valueResultState result)) of
    Just obligation ->
      assert
        (obligationProposition obligation == required)
        "residual obligation lost the exact consumed subject"
    Nothing -> Left "residual obligation was not emitted"

testSubjectIndependentLinear :: Either String ()
testSubjectIndependentLinear = do
  state <- withBinding Linear payload bytes7 emptyCheckState
  let expected = TyRefined (name "s") bytes7 Truth
  result <- mapLeft show $ checkValue (VVar payload) expected state
  assert (ownerAbsent payload result) "subject-independent refinement failed to consume owner"

testBorrowedSubjectRejects :: Either String ()
testBorrowedSubjectRejects = do
  state0 <- withBinding Linear payload bytes7 emptyCheckState
  borrowedContext <- mapLeft show $ startSharedLoan payload (resourceContext state0)
  let state = state0 { resourceContext = borrowedContext }
  case checkValue (VVar payload) reflexiveLengthType state of
    Left (ValueResourceError (OwnerBorrowed owner)) ->
      assert (owner == payload) "borrow rejection named the wrong owner"
    other -> Left ("borrowed subject was not rejected before refinement checking: " ++ show other)

testUnrestrictedSubject :: Either String ()
testUnrestrictedSubject = do
  state <- withBinding Unrestricted payload bytes7 emptyCheckState
  result <- mapLeft show $ checkValue (VVar payload) reflexiveLengthType state
  assert
    (Map.member payload (unrestrictedBindings (resourceContext (valueResultState result))))
    "unrestricted subject was removed"

testMalformedPredicateRejects :: Either String ()
testMalformedPredicateRejects = do
  state <- withBinding Linear payload bytes7 emptyCheckState
  let malformed = TyRefined
        (name "s")
        bytes7
        (Equal (RefLen (RefVar (name "s"))) (RefBool True))
  case checkValue (VVar payload) malformed state of
    Left (ValueRefinementError (RefinementSortError (EqualitySortMismatch _ _))) -> Right ()
    other -> Left ("malformed predicate bypassed sort checking: " ++ show other)

testMissingEvidenceNotMissingSubject :: Either String ()
testMissingEvidenceNotMissingSubject = do
  state <- withBinding Linear payload bytes7 emptyCheckState
  let required = Atom "NeedsAudit" [RefVar payload]
  case checkValue (VVar payload) opaqueRequirementType state of
    Left (ValueRefinementError (MissingEvidence actual)) ->
      assert (actual == required) "missing-evidence rejection changed the subject"
    Left (ValueRefinementError (RefinementSortError (UnknownRefinementVariable missing))) ->
      Left ("consumed subject remained logically invisible: " ++ show missing)
    other -> Left ("unexpected opaque-refinement result: " ++ show other)

isDefinitionalEvidence :: EvidenceUse -> Bool
isDefinitionalEvidence evidenceUse =
  case evidenceUse of
    EvidenceByDefinition _ -> True
    _ -> False

ownerAbsent :: Name -> ValueResult -> Bool
ownerAbsent owner result =
  let context = resourceContext (valueResultState result)
  in not
    ( Map.member owner (affineBindings context)
        || Map.member owner (linearBindings context)
    )

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode binding ty state = do
  context <- mapLeft show $ insertBinding mode binding ty (resourceContext state)
  Right (state { resourceContext = context })

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right