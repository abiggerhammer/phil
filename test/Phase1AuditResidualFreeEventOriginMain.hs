{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Assurance
  ( OriginalCheckEventClosureError (..)
  , closeOriginalCheckEventBundle
  , resolveOriginalCheckEvent
  )
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import qualified Phil.Core.Discharge as Discharge
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValue, checkValueWithResidual)
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ run "C01" "closed residual-free check remains valid" closedCheckRemainsValid
    , run "C02" "caller spec cannot manufacture closed-event origin" closedFinalClosureRequiresProducerAssociation
    , run "C03" "different caller spec cannot relabel the same closed result" closedRelabelRequiresProducerAssociation
    , run "C04" "carried residual-free fact remains valid" carriedCheckRemainsValid
    , run "C05" "caller spec cannot manufacture carried-event origin" carriedFinalClosureRequiresProducerAssociation
    ]
  unless (and results) exitFailure
  putStrLn "COMPLETE residual_free_event_origin_controls=5"

run :: String -> String -> Either String () -> IO Bool
run ident label result =
  case result of
    Right () -> putStrLn ("PASS " <> ident <> " " <> label) >> pure True
    Left detail -> putStrLn ("FAIL " <> ident <> " " <> detail) >> pure False

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False detail = Left detail

specA, specB :: ResidualSpec
specA = ResidualSpec
  (ObligationId "audit.residual-free.original")
  "producer-A"
  "scope-A"
  "point-A"
specB = ResidualSpec
  (ObligationId "audit.residual-free.relabel")
  "producer-B"
  "scope-B"
  "point-B"

subject, payload :: Name
subject = Name "subject"
payload = Name "payload"

boundTy :: Ty
boundTy = TyRefined subject (TyUInt 8)
  (LessEqual (RefToNat (RefVar subject)) (RefNat 1))

closedGoal :: Proposition
closedGoal = LessEqual (RefToNat (RefUInt 8 0)) (RefNat 1)

carriedGoal :: Proposition
carriedGoal = LessEqual (RefToNat (RefVar payload)) (RefNat 1)

closedResult :: Either String ValueResult
closedResult = do
  result <- right $ checkValueWithResidual specA (VUInt 8 0) boundTy emptyCheckState
  ensure (Map.null (residualObligations (valueResultState result)))
    "closed result unexpectedly emitted a residual"
  ensure (EvidenceByDefinition closedGoal `elem` valueResultEvidence result)
    "closed definition evidence disappeared"
  pure result

carriedResult :: Either String ValueResult
carriedResult = do
  source <- right $ checkValue (VUInt 8 0) boundTy emptyCheckState
  context <- right $
    insertBinding Unrestricted payload (valueResultType source) (resourceContext emptyCheckState)
  let before = emptyCheckState { resourceContext = context }
  result <- right $ checkValueWithResidual specA (VVar payload) boundTy before
  ensure (resourceContext (valueResultState result) == beforeContext before)
    "carried check changed unrestricted ownership state"
  ensure (Map.null (residualObligations (valueResultState result)))
    "carried result unexpectedly emitted a residual"
  ensure (EvidenceByBinding payload carriedGoal `elem` valueResultEvidence result)
    "carried binding evidence disappeared"
  pure result
  where
    beforeContext = resourceContext

closedCheckRemainsValid :: Either String ()
closedCheckRemainsValid = do
  result <- closedResult
  resolved <- right $
    resolveOriginalCheckEvent emptyStaticContext Discharge.emptyDischargePolicy specA result
  case Discharge.resolvedDisposition resolved of
    Discharge.StaticallyDischarged _ -> Right ()
    other -> Left ("closed check stopped resolving statically: " <> show other)

carriedCheckRemainsValid :: Either String ()
carriedCheckRemainsValid = do
  result <- carriedResult
  resolved <- right $
    resolveOriginalCheckEvent emptyStaticContext Discharge.emptyDischargePolicy specA result
  case Discharge.resolvedDisposition resolved of
    Discharge.StaticallyDischarged (Discharge.StaticByEvidence actual)
      | actual == payload -> Right ()
    other -> Left ("carried check stopped using its real evidence: " <> show other)

closedFinalClosureRequiresProducerAssociation :: Either String ()
closedFinalClosureRequiresProducerAssociation = do
  result <- closedResult
  expectProducerAssociationRequired specA result

closedRelabelRequiresProducerAssociation :: Either String ()
closedRelabelRequiresProducerAssociation = do
  result <- closedResult
  expectProducerAssociationRequired specB result

carriedFinalClosureRequiresProducerAssociation :: Either String ()
carriedFinalClosureRequiresProducerAssociation = do
  result <- carriedResult
  expectProducerAssociationRequired specA result

-- The final closure must reject before touching downstream manifest inputs.
-- These sentinels make that ordering part of the regression: if the accepting
-- path ever tries to use caller-supplied packaging before establishing producer
-- association, the test fails loudly rather than silently constructing a fake
-- package.
expectProducerAssociationRequired :: ResidualSpec -> ValueResult -> Either String ()
expectProducerAssociationRequired eventSpec result =
  case closeOriginalCheckEventBundle
      (error "handoff config evaluated before producer association")
      emptyStaticContext
      Discharge.emptyDischargePolicy
      eventSpec
      result
      (error "bundle evaluated before producer association")
      (error "assurance policy evaluated before producer association")
      (error "verification context evaluated before producer association")
      (error "ledger evaluated before producer association")
      (error "selection evaluated before producer association")
      Map.empty
      Map.empty of
    Left OriginalCheckEventClosureProducerAssociationRequired -> Right ()
    other -> Left ("residual-free final closure did not fail at producer origin: " <> show other)
