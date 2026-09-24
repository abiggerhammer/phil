{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Phil.Assurance as A
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import qualified Phil.Core.Discharge as D
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValue, checkValueWithResidual)
import System.Exit (exitFailure)

-- Independent positive/preservation controls over authentic checker results.
-- No returned ValueResult, evidence list, residual record, or context is edited.
-- Supplied Core bindings are explicit premises, not a source-to-native claim.
right :: Show e => Either e a -> Either String a
right = either (Left . show) Right
ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False message = Left message

subject, a, b, owner :: Name
subject = Name "subject"
a = Name "a"
b = Name "b"
owner = Name "owner"

spec :: ResidualSpec
spec = ResidualSpec (ObligationId "independent.endpoint.root")
  "EndpointBoundaryReview" "independent.endpoint.scope" "before-consumer"

bind :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
bind mode name ty state = do
  context <- right $ insertBinding mode name ty (resourceContext state)
  pure state { resourceContext = context }

runtimeFor :: Obligation -> D.RuntimeBinding
runtimeFor obligation = D.RuntimeBinding
  { D.runtimeObligationId = obligationId obligation
  , D.runtimeProposition = obligationProposition obligation
  , D.runtimeRequiredPoint = obligationRequiredPoint obligation
  , D.runtimeValidator = "independent-declared-validator"
  , D.runtimeSuccessEvidence = TyProof (obligationProposition obligation)
  , D.runtimeFailureClass = "ValidationFailure"
  , D.runtimeResourceContract = "preserve unrelated resources"
  , D.runtimeCostRef = "independent.endpoint.cost"
  }

policyFor :: ValueResult -> Either String D.DischargePolicy
policyFor result = foldl add (Right D.emptyDischargePolicy)
  (Map.elems (residualObligations (valueResultState result)))
  where
    add acc obligation = do
      policy <- acc
      right $ D.bindRuntime (runtimeFor obligation) policy

coordinates :: A.EvidenceSubjectEndpoint -> (Int, Int, Name)
coordinates endpoint =
  let occurrence = A.evidenceEndpointOccurrence endpoint
  in (A.evidenceSubjectUseIndex occurrence,
      A.evidenceSubjectOccurrenceIndex occurrence,
      A.evidenceSubjectName occurrence)

repeatedEndpoints :: Either String ()
repeatedEndpoints = do
  first <- bind Unrestricted a (TyUInt 8) emptyCheckState
  before <- bind Unrestricted b (TyUInt 8) first
  let goal = Atom "endpoint-label-not-a-variable" [RefVar a, RefVar b, RefVar a]
  result <- right $ checkValueWithResidual spec (VBool True)
    (TyRefined subject TyBool goal) before
  ensure (valueResultEvidence result == [EvidenceResidual (residualObligationId spec) goal])
    "fixture did not produce the exact one-use residual"
  endpoints <- right $ A.actualEvidenceSubjectEndpoints spec result
  ensure (map coordinates endpoints == [(1,1,a),(1,2,b),(1,3,a)])
    "endpoint positions, order, multiplicity or parent use changed"
  case endpoints of
    [ea,eb,eaAgain] -> do
      ensure (A.evidenceEndpointSource ea == A.evidenceEndpointSource eaAgain)
        "repeated occurrences acquired different semantic subject keys"
      ensure (A.evidenceEndpointSource ea /= A.evidenceEndpointSource eb)
        "distinct captured subjects collapsed"
    _ -> Left "wrong endpoint count"
  ensure (all (\e -> A.evidenceEndpointSource e == A.evidenceEndpointTarget e) endpoints)
    "identity-only route manufactured a rebase"
  ensure (resourceContext before == resourceContext (valueResultState result))
    "endpoint fixture changed unrestricted resources"

closedPending :: Either String ()
closedPending = do
  let goal = LessThan (RefOpaque SortNat "independent.closed.pending") (RefNat 5)
  result <- right $ checkValueWithResidual spec (VBool True)
    (TyRefined subject TyBool goal) emptyCheckState
  let expectedUse = EvidenceResidual (residualObligationId spec) goal
      pending = residualObligations (valueResultState result)
  ensure (valueResultEvidence result == [expectedUse]) "closed pending fixture lost its residual"
  ensure (Map.size pending == 1) "closed pending fixture did not retain one obligation"
  case A.actualEvidenceUseInventory result of
    [A.ActualCheckedClosedEvidenceUse 1 use] ->
      ensure (use == expectedUse) "closed classification changed the evidence disposition"
    other -> Left ("closed residual inventory changed: " <> show other)
  endpoints <- right $ A.actualEvidenceSubjectEndpoints spec result
  ensure (null endpoints) "subject-closed residual acquired fabricated endpoints"
  policy <- policyFor result
  resolved <- right $ A.resolveOriginalCheckEvent emptyStaticContext policy spec result
  case D.resolvedDisposition resolved of
    D.RuntimeBound binding -> do
      ensure (D.runtimeObligationId binding == residualObligationId spec)
        "runtime responsibility changed identity"
      ensure (D.runtimeProposition binding == goal) "runtime responsibility changed proposition"
    other -> Left ("subject-closed was confused with static discharge: " <> show other)
  ensure (residualObligations (valueResultState result) == pending)
    "inventory or resolution changed original pending state"
  -- RuntimeBound is a declared checking responsibility, not validator execution.

consumedRefined :: Mode -> Either String ()
consumedRefined mode = do
  let originalType = TyRefined subject (TyUInt 8)
        (LessEqual (RefToNat (RefVar subject)) (RefNat 1))
      expected = TyRefined subject (TyUInt 8)
        (LessThan (RefToNat (RefVar subject)) (RefNat 5))
  literal <- right $ checkValue (VUInt 8 0) originalType emptyCheckState
  before <- bind mode owner (valueResultType literal) emptyCheckState
  result <- right $ checkValueWithResidual spec (VVar owner) expected before
  let context = resourceContext (valueResultState result)
      absent = all (Map.notMember owner)
        [unrestrictedBindings context, affineBindings context, linearBindings context]
  ensure absent "restricted original owner was not consumed"
  endpoints <- right $ A.actualEvidenceSubjectEndpoints spec result
  ensure (not (null endpoints)) "consumed refined subject lost all endpoints"
  ensure (all (\e -> A.originalEventSubjectName (A.evidenceEndpointSource e) == owner
                 && A.originalEventSubjectType (A.evidenceEndpointSource e) == valueResultType literal)
              endpoints)
    "consumed subject lost its exact captured refined interpretation"
  policy <- policyFor result
  resolved <- right $ A.resolveOriginalCheckEvent emptyStaticContext policy spec result
  ensure (obligationId (D.resolvedObligation resolved) == residualObligationId spec)
    "original-event reconstruction changed the root"
  ensure (resourceContext (valueResultState result) == context && absent)
    "original-event reconstruction restored ownership"

main :: IO ()
main = do
  outcomes <- sequence
    [ report "P01" "repeated occurrences keep positions and share the same subject key" repeatedEndpoints
    , report "P02" "subject-closed residual retains exact runtime checking responsibility" closedPending
    , report "P03" "consumed affine refined subject retains endpoints and reconstructs" (consumedRefined Affine)
    , report "P04" "consumed linear refined subject retains endpoints and reconstructs" (consumedRefined Linear)
    ]
  putStrLn "COMPLETE endpoint_preservation_groups=4"
  unless (and outcomes) exitFailure

report :: String -> String -> Either String () -> IO Bool
report key label outcome = case outcome of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left err -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> err) >> pure False
