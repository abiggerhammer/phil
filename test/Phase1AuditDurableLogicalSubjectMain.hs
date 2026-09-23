{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker
  ( CheckState (..)
  , LogicalSubjectSupport (..)
  , emptyCheckState
  )
import Phil.Core.Context
  ( ResourceContext (..)
  , insertBinding
  )
import Phil.Core.Discharge
  ( DischargeError (..)
  , ObligationDisposition (..)
  , ResolvedObligation (..)
  , RuntimeBinding (..)
  , bindRuntime
  , emptyDischargePolicy
  , resolveObligation
  )
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Refinement (ResidualSpec (..))
import Phil.Core.SortCheck (SortError (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , Name (Name)
  , Obligation (..)
  , ObligationId (ObligationId)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Core.Value
  ( ValueResult (..)
  , checkValueWithResidual
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "R01 residual records exact durable logical subject typing" testSupportRecorded
    , test "R02 exact returned residual is interpretable after consumption" testResolverInterpretsConsumedSubject
    , test "R03 runtime disposition resolves under durable logical subject" testRuntimeResolution
    , test "R04 same-spelled replacement cannot override durable subject typing" testSpellingReuseIsolation
    , test "R05 mismatched obligation metadata cannot borrow captured support" testExactObligationIsolation
    , test "C01 durable typing does not restore consumed ownership" testOwnershipRemainsConsumed
    ]
  unless (and results) exitFailure

payload :: Name
payload = Name "payload"

bytes7 :: Ty
bytes7 = TyBytes (RefNat 7)

required :: Proposition
required = LessEqual (RefNat 1) (RefLen (RefVar payload))

residualSpec :: ResidualSpec
residualSpec = ResidualSpec
  { residualObligationId = ObligationId "audit.durable-subject"
  , residualOrigin = "phase1-audit-durable-subject"
  , residualScope = "component:durable-subject"
  , residualRequiredPoint = "after payload consumption"
  }

targetType :: Ty
targetType =
  TyRefined
    (Name "subject")
    bytes7
    (LessEqual (RefNat 1) (RefLen (RefVar (Name "subject"))))

setupResidual :: Either String (Obligation, CheckState)
setupResidual = do
  state <- withBinding Linear payload bytes7 emptyCheckState
  result <- mapLeft show $
    checkValueWithResidual residualSpec (VVar payload) targetType state
  let returned = valueResultState result
  obligation <- maybe (Left "missing emitted residual") Right $
    Map.lookup (residualObligationId residualSpec) (residualObligations returned)
  assert (obligationProposition obligation == required)
    "emitted residual changed the exact consumed subject"
  Right (obligation, returned)

testSupportRecorded :: Either String ()
testSupportRecorded = do
  (obligation, returned) <- setupResidual
  support <- maybe (Left "missing durable logical subject support") Right $
    Map.lookup (obligationId obligation) (residualLogicalSubjects returned)
  assert (logicalSupportObligation support == obligation)
    "durable support is not bound to the exact emitted obligation"
  assert (logicalSupportBindings support == Map.singleton payload bytes7)
    "durable support did not preserve exact Bytes[7] subject typing"
  assert (Map.null (logicalTypingContext returned))
    "durable support leaked into ambient logical typing state"

testResolverInterpretsConsumedSubject :: Either String ()
testResolverInterpretsConsumedSubject = do
  (obligation, returned) <- setupResidual
  case resolveObligation emptyStaticContext returned emptyDischargePolicy obligation of
    Left (UnresolvedObligation actualId actualProposition) -> do
      assert (actualId == obligationId obligation) "resolver changed obligation id"
      assert (actualProposition == required) "resolver changed canonical proposition"
    Left (DischargeFocusingError (FocusSortError (UnknownRefinementVariable missing))) ->
      Left ("durable subject remained uninterpretable: " ++ show missing)
    other -> Left ("unexpected empty-policy resolution: " ++ show other)

testRuntimeResolution :: Either String ()
testRuntimeResolution = do
  (obligation, returned) <- setupResidual
  let binding = runtimeFor obligation
  policy <- mapLeft show $ bindRuntime binding emptyDischargePolicy
  resolved <- mapLeft show $ resolveObligation emptyStaticContext returned policy obligation
  case resolvedDisposition resolved of
    RuntimeBound actual -> assert (actual == binding) "resolver changed runtime binding"
    other -> Left ("durable subject did not reach runtime disposition: " ++ show other)

testSpellingReuseIsolation :: Either String ()
testSpellingReuseIsolation = do
  (obligation, returned) <- setupResidual
  replacement <- withBinding Unrestricted payload TyBool returned
  let binding = runtimeFor obligation
  policy <- mapLeft show $ bindRuntime binding emptyDischargePolicy
  resolved <- mapLeft show $ resolveObligation emptyStaticContext replacement policy obligation
  case resolvedDisposition resolved of
    RuntimeBound actual -> assert (actual == binding) "same-spelled replacement changed disposition"
    other -> Left ("same-spelled replacement displaced durable subject support: " ++ show other)
  let context = resourceContext replacement
  assert (Map.lookup payload (unrestrictedBindings context) == Just TyBool)
    "control replacement was not present"
  assert (Map.notMember payload (linearBindings context))
    "original linear owner was restored"
  support <- maybe (Left "durable support disappeared after spelling reuse") Right $
    Map.lookup (obligationId obligation) (residualLogicalSubjects replacement)
  assert (logicalSupportBindings support == Map.singleton payload bytes7)
    "same-spelled replacement rewrote durable subject typing"

testExactObligationIsolation :: Either String ()
testExactObligationIsolation = do
  (obligation, returned) <- setupResidual
  replacement <- withBinding Unrestricted payload TyBool returned
  let tampered = obligation { obligationOrigin = "different-origin" }
  case resolveObligation emptyStaticContext replacement emptyDischargePolicy tampered of
    Left (DischargeFocusingError (FocusSortError (InvalidLengthOperand term SortBool))) ->
      assert (term == RefVar payload)
        "metadata mismatch failed for an unrelated term"
    other -> Left ("mismatched obligation reused captured logical support: " ++ show other)

testOwnershipRemainsConsumed :: Either String ()
testOwnershipRemainsConsumed = do
  (_, returned) <- setupResidual
  let context = resourceContext returned
  assert (Map.notMember payload (unrestrictedBindings context))
    "consumed owner became unrestricted"
  assert (Map.notMember payload (affineBindings context))
    "consumed owner became affine"
  assert (Map.notMember payload (linearBindings context))
    "consumed linear owner was restored"

runtimeFor :: Obligation -> RuntimeBinding
runtimeFor obligation = RuntimeBinding
  { runtimeObligationId = obligationId obligation
  , runtimeProposition = obligationProposition obligation
  , runtimeRequiredPoint = obligationRequiredPoint obligation
  , runtimeValidator = "durable-subject-validator"
  , runtimeSuccessEvidence = TyProof (obligationProposition obligation)
  , runtimeFailureClass = "ValidationFailure"
  , runtimeResourceContract = "logical subject only; no ownership restoration"
  , runtimeCostRef = "audit"
  }

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode binding ty state = do
  context <- mapLeft show $ insertBinding mode binding ty (resourceContext state)
  Right state { resourceContext = context }

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
