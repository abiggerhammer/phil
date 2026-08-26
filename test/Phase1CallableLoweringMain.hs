{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Callable
import Phil.Core.CallableRefinement
import Phil.Core.CallableScope (LoanScopeKey (..))
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..), Outcome (..))
import Phil.Systems.CallableLowering
import Phil.Systems.IR (CostShape (..), emptyCostShape)
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-016 code pointer plus environment preserves callable semantics" baselineAccepts
    , test "CALL-016 representation identity is nonsemantic" representationIdentityIsNonsemantic
    , test "CALL-016 representation choice is nonsemantic" representationChoiceIsNonsemantic
    , test "CALL-016 raw pointer coincidence does not repair contract mismatch" pointerCannotRepairContractMismatch
    , test "CALL-016 callable machine shape is preserved" machineShapeMismatchRejects
    , test "CALL-016 callable occurrence identity is preserved" occurrenceMismatchRejects
    , test "CALL-016 closure structural mode is preserved" structuralModeMismatchRejects
    , test "CALL-016 captured subject and authority relation is preserved" captureSubjectMismatchRejects
    , test "CALL-016 callee transition is preserved" calleeTransitionMismatchRejects
    , test "CALL-016 caller authority relation is preserved" callerAuthorityMismatchRejects
    , test "CALL-016 captured internal authority is preserved" internalAuthorityMismatchRejects
    , test "CALL-016 semantic effect bound is preserved" effectBoundMismatchRejects
    , test "CALL-016 modeled failure surface is preserved" failureMismatchRejects
    , test "CALL-016 loan validity projection is preserved" loanMismatchRejects
    , test "CALL-016 target helper effects require explicit accounting" unaccountedEffectsReject
    , test "CALL-016 target failures require explicit accounting" unaccountedFailuresReject
    , test "CALL-016 target assumptions require explicit accounting" unaccountedAssumptionsReject
    , test "CALL-016 target carriers require explicit accounting" unaccountedCarriersReject
    , test "CALL-016 target allocation cost requires explicit accounting" unaccountedCostReject
    , test "CALL-016 explicit realization accounting admits target consequences" explicitTargetAccountingAccepts
    , test "CALL-016 capture and authority ordering is canonical" semanticOrderingIsCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

baselineAccepts :: Either String ()
baselineAccepts = assertAccepts sourceFacts targetFacts accounting

representationIdentityIsNonsemantic :: Either String ()
representationIdentityIsNonsemantic = do
  assertAccepts sourceFacts targetFacts accounting
  assertAccepts sourceFacts
    (targetFacts { targetCallableRepresentationIdentity = Just "ptr:0xfeedface" })
    accounting

representationChoiceIsNonsemantic :: Either String ()
representationChoiceIsNonsemantic =
  assertAccepts sourceFacts
    (targetFacts
      { targetCallableRepresentation = DefunctionalizedCallable "closure-tag-7"
      , targetCallableRepresentationIdentity = Just "tag:7"
      })
    accounting

pointerCannotRepairContractMismatch :: Either String ()
pointerCannotRepairContractMismatch =
  let badTarget = targetFacts
        { targetCallableContractRevision = InterfaceRevision "callable.other.v1"
        , targetCallableRepresentationIdentity = targetCallableRepresentationIdentity targetFacts
        }
  in case checkCallableLoweringCorrespondence sourceFacts badTarget accounting of
    Left (CallableLoweringContractRevisionMismatch expected actual) -> do
      assert (expected == contractRevision) "wrong expected contract revision"
      assert (actual == InterfaceRevision "callable.other.v1") "wrong actual contract revision"
    other -> Left ("raw pointer coincidence repaired contract mismatch: " <> show other)

machineShapeMismatchRejects :: Either String ()
machineShapeMismatchRejects =
  case checkCallableLoweringCorrespondence sourceFacts
      (targetFacts { targetCallableMachineShape = otherMachineShape }) accounting of
    Left (CallableLoweringMachineShapeMismatch expected actual) -> do
      assert (expected == machineShape) "wrong expected callable machine shape"
      assert (actual == otherMachineShape) "wrong actual callable machine shape"
    other -> Left ("callable machine-shape mismatch did not reject: " <> show other)

occurrenceMismatchRejects :: Either String ()
occurrenceMismatchRejects =
  case checkCallableLoweringCorrespondence sourceFacts
      (targetFacts { targetCallableOccurrence = Just otherCallableOccurrence }) accounting of
    Left (CallableLoweringOccurrenceMismatch expected actual) -> do
      assert (expected == Just callableOccurrence) "wrong expected occurrence"
      assert (actual == Just otherCallableOccurrence) "wrong actual occurrence"
    other -> Left ("callable occurrence mismatch did not reject: " <> show other)

structuralModeMismatchRejects :: Either String ()
structuralModeMismatchRejects =
  case checkCallableLoweringCorrespondence sourceFacts
      (targetFacts { targetCallableStructuralMode = Unrestricted }) accounting of
    Left (CallableLoweringStructuralModeMismatch expected actual) -> do
      assert (expected == Linear) "wrong expected structural mode"
      assert (actual == Unrestricted) "wrong actual structural mode"
    other -> Left ("structural mode weakening did not reject: " <> show other)

captureSubjectMismatchRejects :: Either String ()
captureSubjectMismatchRejects =
  let badCapture = capturedOwnerSemantic
        { callableCaptureSemanticSubject = Just "blob.002" }
      badTarget = targetFacts
        { targetCallableCaptures = Map.singleton capturedOwner badCapture }
  in case checkCallableLoweringCorrespondence sourceFacts badTarget accounting of
    Left (CallableLoweringCaptureMismatch expected actual) -> do
      assert (expected == sourceCaptures) "wrong expected capture map"
      assert (actual == Map.singleton capturedOwner badCapture) "wrong actual capture map"
    other -> Left ("captured subject mismatch did not reject: " <> show other)

calleeTransitionMismatchRejects :: Either String ()
calleeTransitionMismatchRejects =
  case checkCallableLoweringCorrespondence sourceFacts
      (targetFacts { targetCallableCalleeTransition = ConsumeCallee }) accounting of
    Left (CallableLoweringCalleeTransitionMismatch expected actual) -> do
      assert (expected == PreserveCallee) "wrong expected callee transition"
      assert (actual == ConsumeCallee) "wrong actual callee transition"
    other -> Left ("callee transition mismatch did not reject: " <> show other)

callerAuthorityMismatchRejects :: Either String ()
callerAuthorityMismatchRejects =
  case checkCallableLoweringCorrespondence sourceFacts
      (targetFacts
        { targetCallableCallerAuthority = Set.fromList [readAuthority, writeAuthority] })
      accounting of
    Left (CallableLoweringCallerAuthorityMismatch expected actual) -> do
      assert (expected == Set.singleton readAuthority) "wrong expected caller authority"
      assert (actual == Set.fromList [readAuthority, writeAuthority]) "wrong actual caller authority"
    other -> Left ("caller authority mismatch did not reject: " <> show other)

internalAuthorityMismatchRejects :: Either String ()
internalAuthorityMismatchRejects =
  case checkCallableLoweringCorrespondence sourceFacts
      (targetFacts { targetCallableInternalAuthority = Set.singleton readAuthority })
      accounting of
    Left (CallableLoweringInternalAuthorityMismatch expected actual) -> do
      assert (expected == internalAuthority) "wrong expected internal authority"
      assert (actual == Set.singleton readAuthority) "wrong actual internal authority"
    other -> Left ("captured authority mismatch did not reject: " <> show other)

effectBoundMismatchRejects :: Either String ()
effectBoundMismatchRejects =
  case checkCallableLoweringCorrespondence sourceFacts
      (targetFacts { targetCallableEffectBound = Set.fromList [readEffect, writeEffect] })
      accounting of
    Left (CallableLoweringEffectBoundMismatch expected actual) -> do
      assert (expected == Set.singleton readEffect) "wrong expected effect bound"
      assert (actual == Set.fromList [readEffect, writeEffect]) "wrong actual effect bound"
    other -> Left ("effect bound mismatch did not reject: " <> show other)

failureMismatchRejects :: Either String ()
failureMismatchRejects =
  let fatal = CallableFatal "target-abort"
  in case checkCallableLoweringCorrespondence sourceFacts
      (targetFacts { targetCallableFailures = Set.fromList [notFoundFailure, fatal] })
      accounting of
    Left (CallableLoweringFailureMismatch expected actual) -> do
      assert (expected == Set.singleton notFoundFailure) "wrong expected failure set"
      assert (actual == Set.fromList [notFoundFailure, fatal]) "wrong actual failure set"
    other -> Left ("modeled failure mismatch did not reject: " <> show other)

loanMismatchRejects :: Either String ()
loanMismatchRejects =
  let expired = LoanScopeKey "loan.expired"
  in case checkCallableLoweringCorrespondence sourceFacts
      (targetFacts { targetCallableLiveLoans = Set.insert expired sourceLoans })
      accounting of
    Left (CallableLoweringLoanScopeMismatch expected actual) -> do
      assert (expected == sourceLoans) "wrong expected loan set"
      assert (actual == Set.insert expired sourceLoans) "wrong actual loan set"
    other -> Left ("expired/additional loan scope did not reject: " <> show other)

unaccountedEffectsReject :: Either String ()
unaccountedEffectsReject =
  case checkCallableLoweringCorrespondence sourceFacts targetFacts
      (accounting { accountedCallableEffects = Set.empty }) of
    Left (CallableLoweringEffectAccountingMismatch expected actual) -> do
      assert (expected == Set.singleton allocationEffect) "wrong target helper effect set"
      assert (Set.null actual) "unexpected accounted helper effect"
    other -> Left ("unaccounted target helper effect did not reject: " <> show other)

unaccountedFailuresReject :: Either String ()
unaccountedFailuresReject =
  let targetFailure = CallableFatal "allocator-failure"
      targetWithFailure = targetFacts
        { targetCallableIntroducedFailures = Set.singleton targetFailure }
      accountingWithoutFailure = accounting
        { accountedCallableFailures = Set.empty }
  in case checkCallableLoweringCorrespondence sourceFacts targetWithFailure accountingWithoutFailure of
    Left (CallableLoweringFailureAccountingMismatch expected actual) -> do
      assert (expected == Set.singleton targetFailure) "wrong target failure set"
      assert (Set.null actual) "unexpected accounted target failure"
    other -> Left ("unaccounted target failure did not reject: " <> show other)

unaccountedAssumptionsReject :: Either String ()
unaccountedAssumptionsReject =
  case checkCallableLoweringCorrespondence sourceFacts targetFacts
      (accounting { accountedCallableAssumptions = Set.empty }) of
    Left (CallableLoweringAssumptionAccountingMismatch expected actual) -> do
      assert (expected == Set.singleton allocatorAssumption) "wrong target assumption set"
      assert (Set.null actual) "unexpected accounted assumption"
    other -> Left ("unaccounted target assumption did not reject: " <> show other)

unaccountedCarriersReject :: Either String ()
unaccountedCarriersReject =
  case checkCallableLoweringCorrespondence sourceFacts targetFacts
      (accounting { accountedCallableCarriers = Set.empty }) of
    Left (CallableLoweringCarrierAccountingMismatch expected actual) -> do
      assert (expected == Set.singleton environmentCarrier) "wrong target carrier set"
      assert (Set.null actual) "unexpected accounted carrier"
    other -> Left ("unaccounted target carrier did not reject: " <> show other)

unaccountedCostReject :: Either String ()
unaccountedCostReject =
  case checkCallableLoweringCorrespondence sourceFacts targetFacts
      (accounting { accountedCallableCost = emptyCostShape }) of
    Left (CallableLoweringCostAccountingMismatch expected actual) -> do
      assert (expected == allocationCost) "wrong target cost shape"
      assert (actual == emptyCostShape) "unexpected accounted cost"
    other -> Left ("unaccounted closure allocation cost did not reject: " <> show other)

explicitTargetAccountingAccepts :: Either String ()
explicitTargetAccountingAccepts =
  let targetFailure = CallableFatal "runtime-helper-failure"
      richerTarget = targetFacts
        { targetCallableIntroducedFailures = Set.singleton targetFailure
        , targetCallableIntroducedEffects = Set.fromList [allocationEffect, helperEffect]
        , targetCallableIntroducedAssumptions = Set.fromList [allocatorAssumption, runtimeAssumption]
        , targetCallableIntroducedCarriers = Set.fromList [environmentCarrier, helperCarrier]
        }
      richerAccounting = accounting
        { accountedCallableFailures = Set.singleton targetFailure
        , accountedCallableEffects = Set.fromList [allocationEffect, helperEffect]
        , accountedCallableAssumptions = Set.fromList [runtimeAssumption, allocatorAssumption]
        , accountedCallableCarriers = Set.fromList [helperCarrier, environmentCarrier]
        }
  in assertAccepts sourceFacts richerTarget richerAccounting

semanticOrderingIsCanonical :: Either String ()
semanticOrderingIsCanonical =
  let sourceReordered = sourceFacts
        { sourceCallableCallerAuthority = Set.fromList [readAuthority]
        , sourceCallableInternalAuthority = Set.fromList [deleteAuthority, readAuthority]
        , sourceCallableCaptures = Map.fromList [(capturedOwner, capturedOwnerSemantic)]
        }
      targetReordered = targetFacts
        { targetCallableCallerAuthority = Set.fromList [readAuthority]
        , targetCallableInternalAuthority = Set.fromList [readAuthority, deleteAuthority]
        , targetCallableCaptures = Map.fromList [(capturedOwner, capturedOwnerSemantic)]
        }
  in assertAccepts sourceReordered targetReordered accounting

assertAccepts
  :: SourceCallableLoweringFacts
  -> TargetCallableLoweringFacts
  -> CallableRealizationAccounting
  -> Either String ()
assertAccepts source target account =
  case checkCallableLoweringCorrespondence source target account of
    Right _ -> Right ()
    Left err -> Left ("lowering correspondence rejected: " <> show err)

contractRevision :: InterfaceRevision
contractRevision = InterfaceRevision "callable.read-closure.v1"

machineShape, otherMachineShape :: CallableMachineShape
machineShape = CallableMachineShape "fn(blob)->bytes"
otherMachineShape = CallableMachineShape "fn(blob)->status"

callableOccurrence, otherCallableOccurrence :: CallableOccurrenceKey
callableOccurrence = CallableOccurrenceKey "closure.read.001"
otherCallableOccurrence = CallableOccurrenceKey "closure.read.002"

capturedOwner :: CaptureOccurrenceKey
capturedOwner = CaptureOccurrenceKey "owner.blob.001"

readAuthority, writeAuthority, deleteAuthority :: CallableAuthorityRequirement
readAuthority = CallableAuthorityRequirement "storage.read"
writeAuthority = CallableAuthorityRequirement "storage.write"
deleteAuthority = CallableAuthorityRequirement "storage.delete"

internalAuthority :: Set.Set CallableAuthorityRequirement
internalAuthority = Set.fromList [readAuthority, deleteAuthority]

readEffect, writeEffect, allocationEffect, helperEffect :: SemanticEffect
readEffect = SemanticEffect "read"
writeEffect = SemanticEffect "write"
allocationEffect = SemanticEffect "target.allocate-closure-environment"
helperEffect = SemanticEffect "target.runtime-helper"

notFoundFailure :: CallableFailure
notFoundFailure = CallableTypedNegative (Outcome "not-found")

sourceLoan :: LoanScopeKey
sourceLoan = LoanScopeKey "loan.local.001"

sourceLoans :: Set.Set LoanScopeKey
sourceLoans = Set.singleton sourceLoan

capturedOwnerSemantic :: CallableCaptureSemantic
capturedOwnerSemantic = CallableCaptureSemantic
  { callableCaptureSemanticMode = Linear
  , callableCaptureSemanticSubject = Just "blob.001"
  , callableCaptureSemanticAuthority = internalAuthority
  }

sourceCaptures :: Map.Map CaptureOccurrenceKey CallableCaptureSemantic
sourceCaptures = Map.singleton capturedOwner capturedOwnerSemantic

sourceFacts :: SourceCallableLoweringFacts
sourceFacts = SourceCallableLoweringFacts
  { sourceCallableContractRevision = contractRevision
  , sourceCallableMachineShape = machineShape
  , sourceCallableOccurrence = Just callableOccurrence
  , sourceCallableStructuralMode = Linear
  , sourceCallableCaptures = sourceCaptures
  , sourceCallableCalleeTransition = PreserveCallee
  , sourceCallableCallerAuthority = Set.singleton readAuthority
  , sourceCallableInternalAuthority = internalAuthority
  , sourceCallableEffectBound = Set.singleton readEffect
  , sourceCallableFailures = Set.singleton notFoundFailure
  , sourceCallableLiveLoans = sourceLoans
  }

allocatorAssumption, runtimeAssumption, environmentCarrier, helperCarrier :: Text
allocatorAssumption = "allocator.available"
runtimeAssumption = "runtime.helper.available"
environmentCarrier = "closure-environment-pointer"
helperCarrier = "runtime-helper-dispatch"

allocationCost :: CostShape
allocationCost = emptyCostShape
  { costAllocationCount = Just "1 per closure construction"
  , costPeakLiveMemory = Just "closure environment size"
  , costFrequency = Just "once per constructed closure"
  }

targetFacts :: TargetCallableLoweringFacts
targetFacts = TargetCallableLoweringFacts
  { targetCallableRepresentation = CodePointerEnvironment
  , targetCallableRepresentationIdentity = Just "ptr:0x1234"
  , targetCallableContractRevision = contractRevision
  , targetCallableMachineShape = machineShape
  , targetCallableOccurrence = Just callableOccurrence
  , targetCallableStructuralMode = Linear
  , targetCallableCaptures = sourceCaptures
  , targetCallableCalleeTransition = PreserveCallee
  , targetCallableCallerAuthority = Set.singleton readAuthority
  , targetCallableInternalAuthority = internalAuthority
  , targetCallableEffectBound = Set.singleton readEffect
  , targetCallableFailures = Set.singleton notFoundFailure
  , targetCallableLiveLoans = sourceLoans
  , targetCallableIntroducedEffects = Set.singleton allocationEffect
  , targetCallableIntroducedFailures = Set.empty
  , targetCallableIntroducedAssumptions = Set.singleton allocatorAssumption
  , targetCallableIntroducedCarriers = Set.singleton environmentCarrier
  , targetCallableIntroducedCost = allocationCost
  }

accounting :: CallableRealizationAccounting
accounting = CallableRealizationAccounting
  { accountedCallableEffects = Set.singleton allocationEffect
  , accountedCallableFailures = Set.empty
  , accountedCallableAssumptions = Set.singleton allocatorAssumption
  , accountedCallableCarriers = Set.singleton environmentCarrier
  , accountedCallableCost = allocationCost
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail