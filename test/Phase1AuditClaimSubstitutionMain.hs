{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Discharge
  ( DischargeError (..)
  , emptyDischargePolicy
  , resolveObligation
  )
import Phil.Core.Focusing
  ( FocusMechanism (..)
  , FocusPlan (..)
  , FocusedRequirement (..)
  , FocusingError (..)
  , canonicalizeProposition
  , focusProposition
  )
import Phil.Core.Static
  ( StaticContext
  , declareOpaqueClaim
  , declareTransparentClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (Unrestricted)
  , Name (Name)
  , Obligation (..)
  , ObligationId (ObligationId)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "C01 caller actual survives later formal-name collision" testCallerActualPreserved
    , test "C02 collision does not become definitionally true" testCollisionNeedsDecision
    , test "C03 obligation consumer cannot statically discharge altered claim" testResolverPreservesCallerSubject
    , test "C04 alpha-renaming a formal preserves instantiated meaning" testFormalRenamingInvariant
    , test "C05 nested caller term survives later formal substitution" testNestedCallerTermPreserved
    , test "C06 repeated actuals still normalize definitionally" testRepeatedActuals
    , test "C07 arity checking is unchanged" testArityControl
    , test "C08 argument-sort checking is unchanged" testSortControl
    , test "C09 opaque claims retain their actual arguments" testOpaqueControl
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

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

withBinding :: Name -> Ty -> CheckState -> Either String CheckState
withBinding binding ty state = do
  context <- mapLeft show $
    insertBinding Unrestricted binding ty (resourceContext state)
  Right state { resourceContext = context }

sameBoolContext :: Either String StaticContext
sameBoolContext = mapLeft show $
  declareTransparentClaim
    "Same"
    [(name "p", SortBool), (name "q", SortBool)]
    (Equal (var "p") (var "q"))
    emptyStaticContext

sameBoolRenamedContext :: Either String StaticContext
sameBoolRenamedContext = mapLeft show $
  declareTransparentClaim
    "SameRenamed"
    [(name "p", SortBool), (name "r", SortBool)]
    (Equal (var "p") (var "r"))
    emptyStaticContext

sameNatContext :: Either String StaticContext
sameNatContext = mapLeft show $
  declareTransparentClaim
    "SameNat"
    [(name "p", SortNat), (name "q", SortNat)]
    (Equal (var "p") (var "q"))
    emptyStaticContext

boolCallerState :: Either String CheckState
boolCallerState = withBinding (name "q") TyBool emptyCheckState

natCallerState :: Either String CheckState
natCallerState = withBinding
  (name "q")
  (TyOpaqueSorted "CallerNat" SortNat)
  emptyCheckState

collisionProposition :: Proposition
collisionProposition = Atom "Same" [var "q", RefBool True]

expectedCollision :: Proposition
expectedCollision = Equal (var "q") (RefBool True)

testCallerActualPreserved :: Either String ()
testCallerActualPreserved = do
  sigma <- sameBoolContext
  state <- boolCallerState
  (canonical, _) <- mapLeft show $
    canonicalizeProposition sigma state collisionProposition
  assert
    (canonical == expectedCollision)
    ("caller q was rewritten by later formal substitution: " ++ show canonical)

testCollisionNeedsDecision :: Either String ()
testCollisionNeedsDecision = do
  sigma <- sameBoolContext
  state <- boolCallerState
  plan <- mapLeft show $ focusProposition sigma state collisionProposition
  assert
    (focusedCanonical (focusGoal plan) == expectedCollision)
    "focused claim lost the caller-relative predicate"
  assert
    (focusedMechanism (focusGoal plan) == FocusNeedsDecisionProcedure)
    "collision case was incorrectly discharged by definition"

testResolverPreservesCallerSubject :: Either String ()
testResolverPreservesCallerSubject = do
  sigma <- sameBoolContext
  state <- boolCallerState
  let target = Obligation
        { obligationId = ObligationId "audit.claim-substitution.c03"
        , obligationProposition = collisionProposition
        , obligationOrigin = "Phase1AuditClaimSubstitutionMain"
        , obligationScope = "claim-substitution"
        , obligationRequiredPoint = "before-consumer"
        }
  case resolveObligation sigma state emptyDischargePolicy target of
    Left (UnresolvedObligation actualId actualProposition) -> do
      assert
        (actualId == obligationId target)
        "resolver changed the obligation id"
      assert
        (actualProposition == expectedCollision)
        ("resolver saw the wrong canonical claim: " ++ show actualProposition)
    other -> Left ("collision obligation did not remain unresolved: " ++ show other)

testFormalRenamingInvariant :: Either String ()
testFormalRenamingInvariant = do
  sigmaA <- sameBoolContext
  sigmaB <- sameBoolRenamedContext
  state <- boolCallerState
  (canonicalA, _) <- mapLeft show $
    canonicalizeProposition sigmaA state (Atom "Same" [var "q", RefBool True])
  (canonicalB, _) <- mapLeft show $
    canonicalizeProposition sigmaB state (Atom "SameRenamed" [var "q", RefBool True])
  assert
    (canonicalA == expectedCollision && canonicalB == expectedCollision)
    ("formal rename changed claim meaning: " ++ show (canonicalA, canonicalB))

testNestedCallerTermPreserved :: Either String ()
testNestedCallerTermPreserved = do
  sigma <- sameNatContext
  state <- natCallerState
  let callerActual = RefAdd (var "q") (RefNat 1)
      expected = Equal callerActual (RefNat 7)
  (canonical, _) <- mapLeft show $
    canonicalizeProposition sigma state (Atom "SameNat" [callerActual, RefNat 7])
  assert
    (canonical == expected)
    ("later formal substitution rewrote a nested caller term: " ++ show canonical)

testRepeatedActuals :: Either String ()
testRepeatedActuals = do
  sigma <- sameBoolContext
  state <- boolCallerState
  (canonical, _) <- mapLeft show $
    canonicalizeProposition sigma state (Atom "Same" [var "q", var "q"])
  assert (canonical == Truth) "equal repeated actuals stopped normalizing to Truth"

testArityControl :: Either String ()
testArityControl = do
  sigma <- sameBoolContext
  state <- boolCallerState
  case focusProposition sigma state (Atom "Same" [var "q"]) of
    Left (ClaimArityMismatch "Same" 2 1) -> Right ()
    other -> Left ("claim arity control changed: " ++ show other)

testSortControl :: Either String ()
testSortControl = do
  sigma <- sameBoolContext
  state <- boolCallerState
  case focusProposition sigma state (Atom "Same" [var "q", RefNat 1]) of
    Left (ClaimArgumentSortMismatch "Same" 1 SortBool SortNat) -> Right ()
    other -> Left ("claim sort control changed: " ++ show other)

testOpaqueControl :: Either String ()
testOpaqueControl = do
  sigma <- mapLeft show $
    declareOpaqueClaim
      "OpaqueSame"
      [(name "p", SortBool), (name "q", SortBool)]
      emptyStaticContext
  state <- boolCallerState
  plan <- mapLeft show $
    focusProposition sigma state (Atom "OpaqueSame" [var "q", RefBool True])
  assert
    (focusedCanonical (focusGoal plan) == Atom "OpaqueSame" [var "q", RefBool True])
    "opaque claim arguments changed"
  assert
    (focusedMechanism (focusGoal plan) == FocusNeedsExplicitMechanism)
    "opaque claim mechanism changed"
