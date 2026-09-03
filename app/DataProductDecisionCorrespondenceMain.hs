module Main (main) where

import DataProductKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-PRODUCT exact distinct elimination accepts" eliminationAccepted
    , test "DATA-PRODUCT arity mismatch rejects" arityRejects
    , test "DATA-PRODUCT duplicate successor rejects" duplicateRejects
    , test "DATA-PRODUCT arity failure has precedence" arityPrecedence
    , test "DATA-PRODUCT consumed owner plus exact restoration accepts" restorationAccepted
    , test "DATA-PRODUCT unconsumed owner rejects restoration" ownerRejects
    , test "DATA-PRODUCT inexact successor restoration rejects" exactnessRejects
    , test "DATA-PRODUCT owner failure has restoration precedence" restorationPrecedence
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

eliminationAccepted :: Either String ()
eliminationAccepted =
  assertEliminationAccepted (decideProductEliminationByFacts True True)

arityRejects :: Either String ()
arityRejects =
  assertEliminationArity (decideProductEliminationByFacts False True)

duplicateRejects :: Either String ()
duplicateRejects =
  assertEliminationDuplicate (decideProductEliminationByFacts True False)

arityPrecedence :: Either String ()
arityPrecedence =
  assertEliminationArity (decideProductEliminationByFacts False False)

restorationAccepted :: Either String ()
restorationAccepted =
  assertRestorationAccepted (decideProductRestorationByFacts True True)

ownerRejects :: Either String ()
ownerRejects =
  assertRestorationOwner (decideProductRestorationByFacts False True)

exactnessRejects :: Either String ()
exactnessRejects =
  assertRestorationExactness (decideProductRestorationByFacts True False)

restorationPrecedence :: Either String ()
restorationPrecedence =
  assertRestorationOwner (decideProductRestorationByFacts False False)

assertEliminationAccepted :: ProductEliminationDecision -> Either String ()
assertEliminationAccepted decision = case decision of
  ProductEliminationAcceptedDecision -> Right ()
  _ -> Left "expected accepted product elimination"

assertEliminationArity :: ProductEliminationDecision -> Either String ()
assertEliminationArity decision = case decision of
  ProductEliminationArityDecision -> Right ()
  _ -> Left "expected product arity rejection"

assertEliminationDuplicate :: ProductEliminationDecision -> Either String ()
assertEliminationDuplicate decision = case decision of
  ProductEliminationDuplicateSuccessorDecision -> Right ()
  _ -> Left "expected duplicate-successor rejection"

assertRestorationAccepted :: ProductRestorationDecision -> Either String ()
assertRestorationAccepted decision = case decision of
  ProductRestorationAcceptedDecision -> Right ()
  _ -> Left "expected accepted product restoration"

assertRestorationOwner :: ProductRestorationDecision -> Either String ()
assertRestorationOwner decision = case decision of
  ProductRestorationOwnerDecision -> Right ()
  _ -> Left "expected product-owner rejection"

assertRestorationExactness :: ProductRestorationDecision -> Either String ()
assertRestorationExactness decision = case decision of
  ProductRestorationExactnessDecision -> Right ()
  _ -> Left "expected product-restoration exactness rejection"
