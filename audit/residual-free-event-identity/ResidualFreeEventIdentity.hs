{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Phil.Assurance as A
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import qualified Phil.Core.Discharge as D
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValue, checkValueWithResidual)
import System.Exit (exitFailure)

-- Positive objects come from the actual checker/resolver. We never edit a
-- ValueResult, checked support record, certificate or resolved disposition.
-- O01/O02 describe an input/output contract, not required rejection: relabelling
-- a freshly rechecked closed fact is not automatically unsafe acceptance.

specA, specB :: ResidualSpec
specA = ResidualSpec (ObligationId "audit.event.original") "origin-A" "scope-A" "point-A"
specB = ResidualSpec (ObligationId "audit.event.recheck") "origin-B" "scope-B" "point-B"

payload, subject :: Name
payload = Name "payload"
subject = Name "subject"

boundTy :: Ty
boundTy = TyRefined subject (TyUInt 8)
  (LessEqual (RefToNat (RefVar subject)) (RefNat 1))

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False problem = Left problem

root :: ResidualSpec -> Proposition -> Obligation
root s proposition = Obligation (residualObligationId s) proposition
  (residualOrigin s) (residualScope s) (residualRequiredPoint s)

staticResolved :: ResidualSpec -> Proposition -> ValueResult -> Either String D.ResolvedObligation
staticResolved s proposition result = do
  resolved <- right $ A.resolveOriginalCheckEvent emptyStaticContext D.emptyDischargePolicy s result
  ensure (D.resolvedObligation resolved == root s proposition) "resolver changed supplied event or actual proposition"
  ensure (null (D.resolvedPrerequisites resolved)) "unexpected prerequisite"
  case D.resolvedDisposition resolved of
    D.StaticallyDischarged _ -> Right resolved
    other -> Left ("expected genuine static discharge: " <> show other)

closed :: ResidualSpec -> Either String ValueResult
closed s = do
  result <- right $ checkValueWithResidual s (VUInt 8 0) boundTy emptyCheckState
  ensure (valueResultTerm result == Just (RefUInt 8 0)) "changed actual literal"
  ensure (valueResultType result == boundTy) "changed actual checked type"
  ensure (Map.null (residualObligations (valueResultState result))) "closed result unexpectedly residual"
  ensure (Map.null (residualLogicalSubjects (valueResultState result))) "closed result acquired residual support"
  ensure (EvidenceByDefinition Truth `elem` valueResultEvidence result) "closed evidence-use missing"
  pure result

liveBefore :: Either String CheckState
liveBefore = do
  value <- right $ checkValue (VUInt 8 0) boundTy emptyCheckState
  context <- right $ insertBinding Unrestricted payload (valueResultType value) (resourceContext emptyCheckState)
  pure emptyCheckState { resourceContext = context }

carried :: ResidualSpec -> Either String ValueResult
carried s = do
  before <- liveBefore
  result <- right $ checkValueWithResidual s (VVar payload) boundTy before
  ensure (resourceContext before == resourceContext (valueResultState result)) "original resource context changed"
  ensure (Map.null (residualObligations (valueResultState result))) "carried result unexpectedly residual"
  ensure (Map.null (residualLogicalSubjects (valueResultState result))) "carried result acquired residual support"
  ensure (EvidenceByBinding payload carriedGoal `elem` valueResultEvidence result) "actual carried evidence missing"
  pure result

carriedGoal :: Proposition
carriedGoal = LessEqual (RefToNat (RefVar payload)) (RefNat 1)

closedGoal :: Proposition
closedGoal = LessEqual (RefToNat (RefUInt 8 0)) (RefNat 1)

pending :: Either String (ValueResult,Obligation)
pending = do
  context <- right $ insertBinding Unrestricted payload (TyUInt 8) (resourceContext emptyCheckState)
  let before = emptyCheckState { resourceContext = context }
  result <- right $ checkValueWithResidual specA (VVar payload) boundTy before
  let wanted = root specA carriedGoal
  ensure (Map.lookup (obligationId wanted) (residualObligations (valueResultState result)) == Just wanted)
    "pending original metadata changed"
  ensure (EvidenceResidual (obligationId wanted) carriedGoal `elem` valueResultEvidence result)
    "pending use missing"
  pure (result,wanted)

metadataRejects :: Either String ()
metadataRejects = do
  (result,wanted) <- pending
  case A.resolveOriginalCheckEvent emptyStaticContext D.emptyDischargePolicy specB result of
    Left (A.OriginalCheckEventResidualMetadataMismatch key expected actual)
      | key == obligationId wanted && expected == specB && actual == wanted -> Right ()
    other -> Left ("pending metadata did not reject exactly: " <> show other)

pendingUnresolved :: Either String ()
pendingUnresolved = do
  (result,wanted) <- pending
  case A.resolveOriginalCheckEvent emptyStaticContext D.emptyDischargePolicy specA result of
    Left (A.OriginalCheckEventDischargeError (D.UnresolvedObligation actual _))
      | actual == wanted -> Right ()
    other -> Left ("unsupported original pending requirement changed: " <> show other)

falseLiteral :: Either String ()
falseLiteral = case checkValueWithResidual specA (VUInt 8 2) boundTy emptyCheckState of
  Left _ -> Right ()
  Right result -> Left ("false closed bound admitted: " <> show result)

closedObservation :: Either String String
closedObservation = do
  a <- closed specA
  b <- closed specB
  ensure (a == b) "closed producer results differ; revise observation rather than claiming lost identity"
  ra <- staticResolved specA closedGoal a
  rb <- staticResolved specB closedGoal a
  ensure (D.resolvedObligation ra /= D.resolvedObligation rb) "distinct supplied events collapsed"
  pure ("producer_results_equal=True; original=" <> show (D.resolvedObligation ra)
    <> "; recheck=" <> show (D.resolvedObligation rb)
    <> "; dispositions=" <> show (D.resolvedDisposition ra,D.resolvedDisposition rb))

carriedObservation :: Either String String
carriedObservation = do
  a <- carried specA
  b <- carried specB
  ensure (a == b) "carried producer results differ; revise observation rather than claiming lost identity"
  ra <- staticResolved specA carriedGoal a
  rb <- staticResolved specB carriedGoal a
  ensure (D.resolvedObligation ra /= D.resolvedObligation rb) "distinct supplied events collapsed"
  pure ("producer_results_equal=True; original=" <> show (D.resolvedObligation ra)
    <> "; recheck=" <> show (D.resolvedObligation rb)
    <> "; dispositions=" <> show (D.resolvedDisposition ra,D.resolvedDisposition rb))

main :: IO ()
main = do
  results <- sequence
    [ test "C01" "genuine residual-free closed check and exact original resolution" (closed specA >>= staticResolved specA closedGoal >> pure ())
    , test "C02" "genuine carried original fact and exact original resolution" (carried specA >>= staticResolved specA carriedGoal >> pure ())
    , test "C03" "pending original retains its complete record" (pending >> pure ())
    , test "C04" "pending metadata mismatch rejects before disposition" metadataRejects
    , test "C05" "unsupported original residual does not become static evidence" pendingUnresolved
    , test "C06" "false closed literal requirement still rejects" falseLiteral
    ]
  observations <- sequence
    [ observe "O01" closedObservation
    , observe "O02" carriedObservation
    ]
  putStrLn "COMPLETE correctness_groups=6 observations=2"
  unless (and results && and observations) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label result = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left problem -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> problem) >> pure False

observe :: String -> Either String String -> IO Bool
observe key result = case result of
  Right detail -> putStrLn ("OBS " <> key <> " " <> detail) >> pure True
  Left problem -> putStrLn ("OBS_SETUP_ERROR " <> key <> " " <> problem) >> pure False
