{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..), LogicalSubjectSupport (..), CheckerError (..)
  , emptyCheckState, emitObligation, withObligationLogicalSubjects )
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Discharge
  ( DischargeError (..), ObligationDisposition (..), ResolvedObligation (..)
  , StaticDischarge (..), RuntimeBinding (..), emptyDischargePolicy
  , bindRuntime, resolveObligation )
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Refinement (ResidualSpec (..))
import Phil.Core.SortCheck (SortError (..), checkPropositionSortsUnder)
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..), Name (..), Obligation (..), ObligationId (..)
  , Proposition (..), RefTerm (..), RefSort (..), Ty (..), Value (..) )
import Phil.Core.Value (ValueResult (..), checkValue, checkValueWithResidual, synthValue)
import System.Exit (exitFailure)

-- Independent correctness driver. No ResolvedObligation, solver certificate,
-- LogicalSubjectSupport or checked token is manufactured here. The Core binding
-- environment is explicitly supplied: a newly bound refined value has first
-- been checked as an actual closed literal. This is not a Surface/CLI adapter.
main :: IO ()
main = do
  results <- sequence [run ident label check | (ident,label,check) <- checks]
  observations <- sequence
    [ observe "O01" (replacementResult BooleanCase (Name "payload"))
    , observe "O02" (replacementResult NumericCase (Name "payload")) ]
  putStrLn "COMPLETE correctness_groups=16 observations=2"
  unless (and results && and observations) exitFailure

checks :: [(String, String, Either String ())]
checks =
  [ ("C01", "exact original Bytes residual and support", exactBytes)
  , ("C02", "original emitted obligation remains unresolved without evidence", emptyPolicy)
  , ("C03", "exact declared runtime disposition; owner remains absent", runtimeCase)
  , ("C04", "later plain Bool spelling does not change saved typing", plainReplacement)
  , ("C05", "all five obligation coordinates isolate logical support", metadataIsolation)
  , ("C06", "logical typing grants no value-use permission", noOwnership)
  , ("C07", "explicit local binder shadows saved logical typing", binderPrecedence)
  , ("C08", "same emission context is idempotent; changed typing conflicts", emissionConflict)
  , ("C09", "distinct residual identities preserve distinct captured types", independentCaptures)
  , ("C10", "differently named checked Bool cannot settle old subject", differentBool)
  , ("C11", "differently named numeric refinement cannot settle old subject", differentNumeric)
  , ("C12", "legitimate exact original-subject proof remains usable", exactOriginalProof)
  , ("C13", "pure closed obligation needs no saved context", pureClosed)
  , ("C14", "support activation does not leak to unmatched obligation", activationIsolation)
  , ("R01", "new same-spelled refined Bool is not evidence for old subject", isolated BooleanCase)
  , ("R02", "new same-spelled numeric bound is not solver support for old subject", isolated NumericCase)
  ]

run :: String -> String -> Either String () -> IO Bool
run ident label result = case result of
  Right () -> putStrLn ("PASS " ++ ident ++ " " ++ label) >> pure True
  Left detail -> putStrLn ("FAIL " ++ ident ++ " " ++ detail) >> pure False

observe :: Show a => String -> Either String a -> IO Bool
observe ident result = case result of
  Right value -> putStrLn ("OBS " ++ ident ++ " " ++ show value) >> pure True
  Left detail -> putStrLn ("OBS_SETUP_ERROR " ++ ident ++ " " ++ detail) >> pure False

ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False detail = Left detail
right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

payload, subject :: Name
payload = Name "payload"
subject = Name "subject"
bytes7 :: Ty
bytes7 = TyBytes (RefNat 7)
bytesRequired :: Proposition
bytesRequired = LessEqual (RefNat 1) (RefLen (RefVar payload))
spec :: Text -> ResidualSpec
spec ident = ResidualSpec (ObligationId ident) "independent-audit" "audit.subject-scope" "after-use"

bind :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
bind mode name ty st = do
  ctx <- right $ insertBinding mode name ty (resourceContext st)
  Right st { resourceContext = ctx }

absent :: Name -> CheckState -> Bool
absent name st = all (Map.notMember name)
  [ unrestrictedBindings (resourceContext st), affineBindings (resourceContext st)
  , linearBindings (resourceContext st) ]

emitted :: Text -> Mode -> Ty -> Proposition -> CheckState -> Either String (Obligation, CheckState)
emitted ident mode base predicate initial = do
  before <- bind mode payload base initial
  result <- right $ checkValueWithResidual (spec ident) (VVar payload)
    (TyRefined subject base predicate) before
  let st = valueResultState result
  obligation <- maybe (Left "setup: expected actual emitted residual") Right $
    Map.lookup (ObligationId ident) (residualObligations st)
  ensure (absent payload st) "setup: original owner did not leave resource context"
  ensure (Map.null (logicalTypingContext st)) "transient context leaked into returned value state"
  Right (obligation, st)

bytesSetup :: Either String (Obligation, CheckState)
bytesSetup = emitted "audit.bytes" Linear bytes7
  (LessEqual (RefNat 1) (RefLen (RefVar subject))) emptyCheckState

resolve :: Obligation -> CheckState -> Either DischargeError ResolvedObligation
resolve obligation st = resolveObligation emptyStaticContext st emptyDischargePolicy obligation

expectUnresolved :: Obligation -> Either DischargeError ResolvedObligation -> Either String ()
expectUnresolved obligation result = case result of
  Left (UnresolvedObligation key proposition) ->
    ensure (key == obligationId obligation && proposition == obligationProposition obligation)
      "unresolved result changed exact identity/proposition"
  other -> Left ("expected exact unresolved old-subject obligation, got " ++ show other)

exactBytes :: Either String ()
exactBytes = do
  (obligation, st) <- bytesSetup
  ensure (obligationProposition obligation == bytesRequired) "original Bytes subject changed"
  saved <- maybe (Left "missing saved support") Right $
    Map.lookup (obligationId obligation) (residualLogicalSubjects st)
  ensure (logicalSupportObligation saved == obligation) "saved metadata not exact"
  ensure (logicalSupportBindings saved == Map.singleton payload bytes7) "saved type not exact"

emptyPolicy :: Either String ()
emptyPolicy = do
  (obligation, st) <- bytesSetup
  expectUnresolved obligation (resolve obligation st)

runtimeFor :: Obligation -> RuntimeBinding
runtimeFor obligation = RuntimeBinding (obligationId obligation) (obligationProposition obligation)
  (obligationRequiredPoint obligation) "declared-audit-validator"
  (TyProof (obligationProposition obligation)) "ValidationFailure" "no restored ownership" "audit.cost"

requireRuntime :: Obligation -> CheckState -> Either String ()
requireRuntime obligation st = do
  let runtime = runtimeFor obligation
  policy <- right $ bindRuntime runtime emptyDischargePolicy
  result <- right $ resolveObligation emptyStaticContext st policy obligation
  ensure (resolvedObligation result == obligation && resolvedDisposition result == RuntimeBound runtime)
    "exact runtime disposition changed"

runtimeCase :: Either String ()
runtimeCase = do
  (obligation, st) <- bytesSetup
  requireRuntime obligation st
  ensure (absent payload st) "owner was restored"

plainReplacement :: Either String ()
plainReplacement = do
  (obligation, st) <- bytesSetup
  replaced <- bind Unrestricted payload TyBool st
  requireRuntime obligation replaced
  ensure (Map.lookup payload (unrestrictedBindings (resourceContext replaced)) == Just TyBool)
    "new resource type was overwritten"

metadataIsolation :: Either String ()
metadataIsolation = do
  (obligation, st) <- bytesSetup
  let changes = [obligation { obligationId = ObligationId "other" }
                ,obligation { obligationOrigin = "other" }
                ,obligation { obligationScope = "other" }
                ,obligation { obligationRequiredPoint = "other" }
                ,obligation { obligationProposition = LessEqual (RefNat 2) (RefLen (RefVar payload)) }]
  mapM_ (\changed -> case resolve changed st of
      Left (DischargeFocusingError (FocusSortError (UnknownRefinementVariable missing))) ->
        ensure (missing == payload) "unrelated missing variable"
      other -> Left ("mismatched record borrowed support: " ++ show other)) changes

noOwnership :: Either String ()
noOwnership = do
  (obligation, st) <- bytesSetup
  let activated = withObligationLogicalSubjects obligation st
  ensure (resourceContext activated == resourceContext st && absent payload activated)
    "activation changed ownership"
  case synthValue (VVar payload) activated of
    Left _ -> Right ()
    other -> Left ("logical typing granted ordinary value use: " ++ show other)

binderPrecedence :: Either String ()
binderPrecedence = do
  (obligation, st) <- bytesSetup
  let active = withObligationLogicalSubjects obligation st
  right $ checkPropositionSortsUnder [(payload,TyBool)] active (Equal (RefVar payload) (RefBool True))
  case checkPropositionSortsUnder [(payload,TyBool)] active bytesRequired of
    Left (InvalidLengthOperand term SortBool) -> ensure (term == RefVar payload) "wrong binder subject"
    other -> Left ("explicit binder did not shadow saved context: " ++ show other)

emissionConflict :: Either String ()
emissionConflict = do
  (obligation, _) <- bytesSetup
  before <- bind Linear payload bytes7 emptyCheckState
  once <- right $ emitObligation obligation before
  twice <- right $ emitObligation obligation once
  ensure (once == twice) "same-context emission is not idempotent"
  (_, consumed) <- bytesSetup
  replaced <- bind Unrestricted payload TyBool consumed
  case emitObligation obligation replaced of
    Left (ConflictingLogicalSubjectSupport key _ _) -> ensure (key == obligationId obligation) "wrong conflict id"
    other -> Left ("changed support silently accepted: " ++ show other)

independentCaptures :: Either String ()
independentCaptures = do
  (first, st1) <- bytesSetup
  (second, st2) <- emitted "audit.bytes.second" Affine (TyBytes (RefNat 8))
    (LessEqual (RefNat 1) (RefLen (RefVar subject))) st1
  requireRuntime first st2
  requireRuntime second st2
  let saved = residualLogicalSubjects st2
      tyFor key = logicalSupportBindings <$> Map.lookup key saved
  ensure (tyFor (obligationId first) == Just (Map.singleton payload bytes7)) "first snapshot overwritten"
  ensure (tyFor (obligationId second) == Just (Map.singleton payload (TyBytes (RefNat 8))))
    "second snapshot not independently retained"

data Case = BooleanCase | NumericCase deriving (Eq, Show)

caseSetup :: Case -> Either String (Obligation, CheckState)
caseSetup which = case which of
  BooleanCase -> emitted "audit.old.bool" Affine TyBool
    (Equal (RefVar subject) (RefBool True)) emptyCheckState
  NumericCase -> emitted "audit.old.uint" Affine (TyUInt 8)
    (LessThan (RefToNat (RefVar subject)) (RefNat 5)) emptyCheckState

-- The replacement is checked independently as a closed literal, including its
-- claimed refinement. Only its successfully returned type is inserted. The
-- supplied Core binding operation is explicitly an audit adapter, not a claim
-- that this driver traverses the full Surface source pipeline.
checkedReplacement :: Case -> Name -> CheckState -> Either String CheckState
checkedReplacement which newName st = do
  let (literal, ty) = case which of
        BooleanCase -> (VBool True, TyRefined subject TyBool (Equal (RefVar subject) (RefBool True)))
        NumericCase -> (VUInt 8 0, TyRefined subject (TyUInt 8)
          (LessEqual (RefToNat (RefVar subject)) (RefNat 1)))
  admitted <- right $ checkValue literal ty st
  ensure (valueResultType admitted == ty) "replacement refinement was not independently checked"
  bind Unrestricted newName (valueResultType admitted) (valueResultState admitted)

replacementResult :: Case -> Name -> Either String (Either DischargeError ResolvedObligation)
replacementResult which newName = do
  (obligation, st) <- caseSetup which
  expectUnresolved obligation (resolve obligation st)
  replacement <- checkedReplacement which newName st
  ensure (residualLogicalSubjects replacement == residualLogicalSubjects st) "replacement changed saved support"
  Right (resolve obligation replacement)

isolated :: Case -> Either String ()
isolated which = do
  (obligation, _) <- caseSetup which
  actual <- replacementResult which payload
  expectUnresolved obligation actual

differentBool, differentNumeric :: Either String ()
differentBool = replacementResult BooleanCase (Name "newPayload") >>= \result -> do
  (obligation, _) <- caseSetup BooleanCase
  expectUnresolved obligation result
differentNumeric = replacementResult NumericCase (Name "newPayload") >>= \result -> do
  (obligation, _) <- caseSetup NumericCase
  expectUnresolved obligation result

exactOriginalProof :: Either String ()
exactOriginalProof = do
  (obligation, st) <- caseSetup BooleanCase
  -- Explicit legitimate Core proof premise about the ORIGINAL logical subject.
  -- This is a positive supplied-authority control, not a generated theorem.
  supported <- bind Unrestricted (Name "originalProof") (TyProof (obligationProposition obligation)) st
  result <- right $ resolve obligation supported
  ensure (resolvedDisposition result == StaticallyDischarged (StaticByEvidence (Name "originalProof")))
    "legitimate original-subject evidence was rejected"

pureClosed :: Either String ()
pureClosed = do
  let obligation = Obligation (ObligationId "closed") (Equal (RefNat 1) (RefNat 1)) "audit" "pure" "now"
  result <- right $ resolve obligation emptyCheckState
  ensure (resolvedDisposition result == StaticallyDischarged StaticByDefinition) "pure closed check failed"

activationIsolation :: Either String ()
activationIsolation = do
  (obligation, st) <- bytesSetup
  let active = withObligationLogicalSubjects obligation st
      other = obligation { obligationScope = "different-event" }
      inactive = withObligationLogicalSubjects other active
  ensure (Map.null (logicalTypingContext inactive)) "transient support survived mismatched activation"
  ensure (resourceContext inactive == resourceContext st) "activation modified resources"
