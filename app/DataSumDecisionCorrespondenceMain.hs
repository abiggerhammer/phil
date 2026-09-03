module Main (main) where

import DataSumKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-SUM declared constructor accepts" constructorDeclared
    , test "DATA-SUM unknown constructor rejects" constructorUnknown
    , test "DATA-SUM consumed aggregate plus exact payload restoration accepts" payloadExact
    , test "DATA-SUM unconsumed aggregate rejects payload restoration" payloadAggregateMissing
    , test "DATA-SUM inexact payload restoration rejects" payloadInexact
    , test "DATA-SUM accounted continuing arm accepts" armAccounted
    , test "DATA-SUM unaccounted continuing arm rejects" armUnaccounted
    , test "DATA-SUM compatible raw branch shapes with join accept" rawCompatible
    , test "DATA-SUM explicit common package with join accepts" explicitPackage
    , test "DATA-SUM compatible plus explicit package still accepts" compatibleAndPackaged
    , test "DATA-SUM hidden branch state without package rejects" hiddenStateRejects
    , test "DATA-SUM failed ordinary join rejects compatible raw shapes" rawJoinFailure
    , test "DATA-SUM failed ordinary join rejects explicit package" packagedJoinFailure
    , test "DATA-SUM failed ordinary join rejects hidden state" hiddenJoinFailure
    , test "DATA-SUM failed ordinary join rejects fully compatible/package state" allFactsButJoin
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

constructorDeclared :: Either String ()
constructorDeclared =
  assertConstructorAccepted (decideConstructorSelectionByFact True)

constructorUnknown :: Either String ()
constructorUnknown =
  assertConstructorUnknown (decideConstructorSelectionByFact False)

payloadExact :: Either String ()
payloadExact =
  assertPayloadAccepted (decideSelectedPayloadRestorationByFacts True True)

payloadAggregateMissing :: Either String ()
payloadAggregateMissing =
  assertPayloadAggregate (decideSelectedPayloadRestorationByFacts False True)

payloadInexact :: Either String ()
payloadInexact =
  assertPayloadExactness (decideSelectedPayloadRestorationByFacts True False)

armAccounted :: Either String ()
armAccounted = assertArmAccepted (decideContinuingArmByFact True)

armUnaccounted :: Either String ()
armUnaccounted = assertArmDisposition (decideContinuingArmByFact False)

rawCompatible :: Either String ()
rawCompatible = assertBranchAccepted (decideBranchConvergenceByFacts True False True)

explicitPackage :: Either String ()
explicitPackage = assertBranchAccepted (decideBranchConvergenceByFacts False True True)

compatibleAndPackaged :: Either String ()
compatibleAndPackaged = assertBranchAccepted (decideBranchConvergenceByFacts True True True)

hiddenStateRejects :: Either String ()
hiddenStateRejects = assertBranchHidden (decideBranchConvergenceByFacts False False True)

rawJoinFailure :: Either String ()
rawJoinFailure = assertBranchJoin (decideBranchConvergenceByFacts True False False)

packagedJoinFailure :: Either String ()
packagedJoinFailure = assertBranchJoin (decideBranchConvergenceByFacts False True False)

hiddenJoinFailure :: Either String ()
hiddenJoinFailure = assertBranchJoin (decideBranchConvergenceByFacts False False False)

allFactsButJoin :: Either String ()
allFactsButJoin = assertBranchJoin (decideBranchConvergenceByFacts True True False)

assertConstructorAccepted :: ConstructorSelectionDecision -> Either String ()
assertConstructorAccepted decision = case decision of
  ConstructorSelectionAcceptedDecision -> Right ()
  ConstructorSelectionUnknownDecision -> Left "expected accepted constructor selection"

assertConstructorUnknown :: ConstructorSelectionDecision -> Either String ()
assertConstructorUnknown decision = case decision of
  ConstructorSelectionUnknownDecision -> Right ()
  ConstructorSelectionAcceptedDecision -> Left "expected unknown constructor rejection"

assertPayloadAccepted :: SelectedPayloadRestorationDecision -> Either String ()
assertPayloadAccepted decision = case decision of
  SelectedPayloadRestorationAcceptedDecision -> Right ()
  _ -> Left "expected accepted selected-payload restoration"

assertPayloadAggregate :: SelectedPayloadRestorationDecision -> Either String ()
assertPayloadAggregate decision = case decision of
  SelectedPayloadAggregateDecision -> Right ()
  _ -> Left "expected aggregate-consumption rejection"

assertPayloadExactness :: SelectedPayloadRestorationDecision -> Either String ()
assertPayloadExactness decision = case decision of
  SelectedPayloadExactnessDecision -> Right ()
  _ -> Left "expected payload-exactness rejection"

assertArmAccepted :: ContinuingArmDecision -> Either String ()
assertArmAccepted decision = case decision of
  ContinuingArmAcceptedDecision -> Right ()
  ContinuingArmPayloadDispositionDecision -> Left "expected accepted continuing arm"

assertArmDisposition :: ContinuingArmDecision -> Either String ()
assertArmDisposition decision = case decision of
  ContinuingArmPayloadDispositionDecision -> Right ()
  ContinuingArmAcceptedDecision -> Left "expected payload-disposition rejection"

assertBranchAccepted :: BranchConvergenceDecision -> Either String ()
assertBranchAccepted decision = case decision of
  BranchConvergenceAcceptedDecision -> Right ()
  _ -> Left "expected accepted branch convergence"

assertBranchHidden :: BranchConvergenceDecision -> Either String ()
assertBranchHidden decision = case decision of
  BranchConvergenceHiddenStateDecision -> Right ()
  _ -> Left "expected hidden-state rejection"

assertBranchJoin :: BranchConvergenceDecision -> Either String ()
assertBranchJoin decision = case decision of
  BranchConvergenceJoinDecision -> Right ()
  _ -> Left "expected ordinary-join rejection"
