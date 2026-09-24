{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import qualified Phil.Assurance as Assurance
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValueWithResidual)
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ run "E01" "every actual subject occurrence receives an exact same-event endpoint" multiSubjectEndpoints
    , run "E02" "endpoint identity is qualified by the validated producer event" eventIdentityIsProducerQualified
    , run "E03" "consumed linear subject keeps logical endpoint without ownership" consumedLinearEndpoint
    , run "E04" "same-spelled ambient replacement cannot retarget old endpoint" replacementDoesNotRetarget
    , run "E05" "unsupported actual occurrence fails closed" unsupportedOccurrenceRejected
    , run "E06" "wrong producer metadata cannot establish endpoint authority" wrongMetadataRejected
    ]
  unless (and results) exitFailure
  putStrLn "COMPLETE evidence_subject_endpoint_controls=6"

run :: String -> String -> Either String () -> IO Bool
run ident label result =
  case result of
    Right () -> putStrLn ("PASS " <> ident <> " " <> label) >> pure True
    Left detail -> putStrLn ("FAIL " <> ident <> " " <> detail) >> pure False

ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False detail = Left detail

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

a, b, payload, binder, ghost :: Name
a = Name "a"
b = Name "b"
payload = Name "payload"
binder = Name "subject"
ghost = Name "ghost"

spec :: ResidualSpec
spec = ResidualSpec
  { residualObligationId = ObligationId "audit.endpoint.root"
  , residualOrigin = "Phase1AuditEvidenceSubjectEndpoints"
  , residualScope = "audit.endpoint.same-event"
  , residualRequiredPoint = "before final consumer"
  }

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode name ty state = do
  context <- right $ insertBinding mode name ty (resourceContext state)
  Right state { resourceContext = context }

uintState :: Either String CheckState
uintState = foldM add emptyCheckState [a, b]
  where
    add state name = withBinding Unrestricted name (TyUInt 8) state

multiSubjectProposition :: Proposition
multiSubjectProposition =
  LessThan
    (RefToNat (RefVar a))
    (RefToNat (RefVar b))

multiSubjectResult :: Either String ValueResult
multiSubjectResult = do
  state <- uintState
  right $
    checkValueWithResidual
      spec
      (VBool True)
      (TyRefined binder TyBool multiSubjectProposition)
      state

endpointNames :: [Assurance.EvidenceSubjectEndpoint] -> [Name]
endpointNames = map (Assurance.originalEventSubjectName . Assurance.evidenceEndpointSource)

endpointTypes :: [Assurance.EvidenceSubjectEndpoint] -> [Ty]
endpointTypes = map (Assurance.originalEventSubjectType . Assurance.evidenceEndpointSource)

multiSubjectEndpoints :: Either String ()
multiSubjectEndpoints = do
  result <- multiSubjectResult
  endpoints <- right $ Assurance.actualEvidenceSubjectEndpoints spec result
  ensure (endpointNames endpoints == [a, b])
    ("expected ordered [a,b] endpoint coverage, got " <> show (endpointNames endpoints))
  ensure (endpointTypes endpoints == [TyUInt 8, TyUInt 8])
    ("unexpected endpoint types: " <> show (endpointTypes endpoints))
  ensure (all sameEndpoint endpoints)
    "supported Phase-1 route inferred a rebase instead of identity transport"
  where
    sameEndpoint endpoint =
      Assurance.evidenceEndpointSource endpoint == Assurance.evidenceEndpointTarget endpoint

eventIdentityIsProducerQualified :: Either String ()
eventIdentityIsProducerQualified = do
  result <- multiSubjectResult
  endpoints <- right $ Assurance.actualEvidenceSubjectEndpoints spec result
  let actualResidualIds =
        [ obligationId'
        | EvidenceResidual obligationId' _ <- valueResultEvidence result
        ]
      expectedEvent = Assurance.OriginalEventIdentity
        { Assurance.originalEventSpec = spec
        , Assurance.originalEventResidualIds = actualResidualIds
        }
      events = map
        (Assurance.originalEventSubjectEvent . Assurance.evidenceEndpointSource)
        endpoints
  ensure (not (null actualResidualIds)) "fixture did not emit a producer residual"
  ensure (all (== expectedEvent) events)
    ("endpoints were not tied to the exact producer event: " <> show events)

consumedLinearResult :: Either String ValueResult
consumedLinearResult = do
  before <- withBinding Linear payload (TyUInt 8) emptyCheckState
  let expected = TyRefined binder (TyUInt 8)
        (LessThan (RefToNat (RefVar binder)) (RefNat 5))
  right $ checkValueWithResidual spec (VVar payload) expected before

consumedLinearEndpoint :: Either String ()
consumedLinearEndpoint = do
  result <- consumedLinearResult
  ensure
    (Map.notMember payload (linearBindings (resourceContext (valueResultState result))))
    "linear owner was unexpectedly restored after checking"
  endpoints <- right $ Assurance.actualEvidenceSubjectEndpoints spec result
  ensure (endpointNames endpoints == [payload])
    ("consumed subject did not retain exactly one logical endpoint: " <> show endpoints)
  ensure (endpointTypes endpoints == [TyUInt 8])
    ("consumed subject endpoint changed type: " <> show (endpointTypes endpoints))
  ensure
    (Map.notMember payload (linearBindings (resourceContext (valueResultState result))))
    "endpoint reflection restored consumed ownership"

replacementDoesNotRetarget :: Either String ()
replacementDoesNotRetarget = do
  result <- consumedLinearResult
  let state = valueResultState result
  replacementContext <- right $
    insertBinding Unrestricted payload TyBool (resourceContext state)
  let replaced = result
        { valueResultState = state { resourceContext = replacementContext }
        }
  endpoints <- right $ Assurance.actualEvidenceSubjectEndpoints spec replaced
  ensure (endpointTypes endpoints == [TyUInt 8])
    ("same-spelled replacement retargeted old endpoint: " <> show endpoints)
  ensure
    (Map.lookup payload (unrestrictedBindings replacementContext) == Just TyBool)
    "replacement fixture did not install the conflicting ambient binding"

unsupportedOccurrenceRejected :: Either String ()
unsupportedOccurrenceRejected = do
  result <- multiSubjectResult
  let fabricatedUse = EvidenceByDefinition (Equal (RefVar ghost) (RefVar ghost))
      tampered = result
        { valueResultEvidence = fabricatedUse : valueResultEvidence result
        }
  case Assurance.actualEvidenceSubjectEndpoints spec tampered of
    Left (Assurance.OriginalCheckEventSubjectEndpointMissing 1 1 name)
      | name == ghost -> Right ()
    other -> Left ("unsupported occurrence did not fail closed: " <> show other)

wrongMetadataRejected :: Either String ()
wrongMetadataRejected = do
  result <- multiSubjectResult
  let wrong = spec { residualScope = "audit.endpoint.other-event" }
  case Assurance.actualEvidenceSubjectEndpoints wrong result of
    Left (Assurance.OriginalCheckEventResidualMetadataMismatch _ _ _) -> Right ()
    other -> Left ("wrong event metadata established endpoint authority: " <> show other)
