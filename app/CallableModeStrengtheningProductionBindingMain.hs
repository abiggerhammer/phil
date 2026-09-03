{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.Callable.ModeDeclaration
import qualified Phil.Core.CallableModeStrengtheningKernelBridge as KernelBridge
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "production derived mode preserves exact capture summary" derivedModePreservesCaptureSummary
    , test "production equal mode accepts before target-reason inspection" equalModeAcceptsBeforeTargetInspection
    , test "production lifecycle strengthening preserves exact result" lifecycleStrengtheningPreservesResult
    , test "production authority strengthening preserves exact result" authorityStrengtheningPreservesResult
    , test "production weakening preserves diagnostic" weakeningPreservesDiagnostic
    , test "production missing justification preserves diagnostic" missingJustificationPreservesDiagnostic
    , test "production target reason preserves diagnostic" targetReasonPreservesDiagnostic
    , test "production wrong contract preserves diagnostic" wrongContractPreservesDiagnostic
    , test "production empty semantic detail preserves diagnostic" emptyJustificationPreservesDiagnostic
    , test "bridge preserves weakening precedence" bridgePreservesWeakeningPrecedence
    , test "bridge accepts exact semantic strengthening" bridgeAcceptsExactStrengthening
    , test "bridge checked-shape minimum mismatch fails first" bridgeShapeMinimumMismatch
    , test "bridge checked-shape selected mismatch fails" bridgeShapeSelectedMismatch
    , test "bridge checked-shape justification mismatch fails" bridgeShapeJustificationMismatch
    , test "bridge checked-shape exact result accepts" bridgeShapeExactAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

derivedModePreservesCaptureSummary :: Either String ()
derivedModePreservesCaptureSummary = do
  captures <- captureSummary [linearCapture]
  checked <- mapLeft show $ checkClosureModeDeclaration contract captures DerivedClosureMode
  assert
    ( checkedClosureMinimumMode checked == Linear
      && checkedClosureSelectedMode checked == Linear
      && checkedClosureModeJustification checked == Nothing
      && checkedClosureCaptureSummary checked == captures )
    "derived production binding changed minimum, selection, justification, or capture summary"

equalModeAcceptsBeforeTargetInspection :: Either String ()
equalModeAcceptsBeforeTargetInspection = do
  captures <- captureSummary [affineCapture]
  let justification = TargetImplementationModeReason "irrelevant equal-mode target note"
  checked <- mapLeft show $ checkClosureModeDeclaration
    contract captures (ExplicitClosureMode Affine (Just justification))
  assert
    ( checkedClosureMinimumMode checked == Affine
      && checkedClosureSelectedMode checked == Affine
      && checkedClosureModeJustification checked == Just justification
      && checkedClosureCaptureSummary checked == captures )
    "equal-mode production path inspected or rewrote an irrelevant justification"

lifecycleStrengtheningPreservesResult :: Either String ()
lifecycleStrengtheningPreservesResult = do
  captures <- captureSummary []
  let justification = LifecycleModeObligation contractRevision "one-shot lifecycle"
  checked <- mapLeft show $ checkClosureModeDeclaration
    contract captures (ExplicitClosureMode Affine (Just justification))
  assert
    ( checkedClosureMinimumMode checked == Unrestricted
      && checkedClosureSelectedMode checked == Affine
      && checkedClosureModeJustification checked == Just justification
      && checkedClosureCaptureSummary checked == captures )
    "lifecycle production binding changed exact checked result"

authorityStrengtheningPreservesResult :: Either String ()
authorityStrengtheningPreservesResult = do
  captures <- captureSummary []
  let justification = AuthorityModeObligation
        contractRevision "nonduplicable delegated authority"
  checked <- mapLeft show $ checkClosureModeDeclaration
    contract captures (ExplicitClosureMode Linear (Just justification))
  assert
    ( checkedClosureMinimumMode checked == Unrestricted
      && checkedClosureSelectedMode checked == Linear
      && checkedClosureModeJustification checked == Just justification
      && checkedClosureCaptureSummary checked == captures )
    "authority production binding changed exact checked result"

weakeningPreservesDiagnostic :: Either String ()
weakeningPreservesDiagnostic = do
  captures <- captureSummary [affineCapture]
  case checkClosureModeDeclaration
      contract captures (ExplicitClosureMode Unrestricted Nothing) of
    Left (ExplicitClosureModeWeakensCaptureMinimum Affine Unrestricted) -> Right ()
    other -> Left ("weakening diagnostic changed: " <> show other)

missingJustificationPreservesDiagnostic :: Either String ()
missingJustificationPreservesDiagnostic = do
  captures <- captureSummary []
  case checkClosureModeDeclaration
      contract captures (ExplicitClosureMode Linear Nothing) of
    Left (StricterClosureModeMissingSemanticJustification Unrestricted Linear) -> Right ()
    other -> Left ("missing-justification diagnostic changed: " <> show other)

targetReasonPreservesDiagnostic :: Either String ()
targetReasonPreservesDiagnostic = do
  captures <- captureSummary []
  let detail = "temporary is destroyed by call instruction"
  case checkClosureModeDeclaration
      contract captures
      (ExplicitClosureMode Affine (Just (TargetImplementationModeReason detail))) of
    Left (TargetImplementationCannotStrengthenClosureMode actualDetail) ->
      assert (actualDetail == detail) "target-reason diagnostic lost exact detail"
    other -> Left ("target-reason diagnostic changed: " <> show other)

wrongContractPreservesDiagnostic :: Either String ()
wrongContractPreservesDiagnostic = do
  captures <- captureSummary []
  let wrongRevision = InterfaceRevision "callable.other.v1"
      justification = LifecycleModeObligation wrongRevision "other lifecycle"
  case checkClosureModeDeclaration
      contract captures (ExplicitClosureMode Affine (Just justification)) of
    Left (StricterClosureModeWrongContract expected actual) ->
      assert
        (expected == contractRevision && actual == wrongRevision)
        "wrong-contract diagnostic lost exact revisions"
    other -> Left ("wrong-contract diagnostic changed: " <> show other)

emptyJustificationPreservesDiagnostic :: Either String ()
emptyJustificationPreservesDiagnostic = do
  captures <- captureSummary []
  let justification = LifecycleModeObligation contractRevision ""
  case checkClosureModeDeclaration
      contract captures (ExplicitClosureMode Affine (Just justification)) of
    Left (StricterClosureModeEmptyJustification Affine) -> Right ()
    other -> Left ("empty-justification diagnostic changed: " <> show other)

bridgePreservesWeakeningPrecedence :: Either String ()
bridgePreservesWeakeningPrecedence =
  assert
    (KernelBridge.classifyExplicitClosureModeFacts
      False True True True True True ==
      KernelBridge.ExplicitClosureModeWeakeningClassification)
    "kernel bridge did not preserve weakening precedence"

bridgeAcceptsExactStrengthening :: Either String ()
bridgeAcceptsExactStrengthening =
  assert
    (KernelBridge.classifyExplicitClosureModeFacts
      True False True False True True ==
      KernelBridge.ExplicitClosureModeStrengthenedClassification)
    "kernel bridge rejected exact semantic strengthening"

bridgeShapeMinimumMismatch :: Either String ()
bridgeShapeMinimumMismatch =
  assert
    (KernelBridge.classifyCheckedClosureModeShapeFacts False False False ==
      KernelBridge.CheckedClosureModeMinimumClassification)
    "shape bridge did not reject minimum mismatch first"

bridgeShapeSelectedMismatch :: Either String ()
bridgeShapeSelectedMismatch =
  assert
    (KernelBridge.classifyCheckedClosureModeShapeFacts True False False ==
      KernelBridge.CheckedClosureModeSelectedClassification)
    "shape bridge did not reject selected mismatch"

bridgeShapeJustificationMismatch :: Either String ()
bridgeShapeJustificationMismatch =
  assert
    (KernelBridge.classifyCheckedClosureModeShapeFacts True True False ==
      KernelBridge.CheckedClosureModeJustificationClassification)
    "shape bridge did not reject justification mismatch"

bridgeShapeExactAccepts :: Either String ()
bridgeShapeExactAccepts =
  assert
    (KernelBridge.classifyCheckedClosureModeShapeFacts True True True ==
      KernelBridge.CheckedClosureModeShapeAcceptedClassification)
    "shape bridge rejected exact production result"

captureSummary :: [ClosureCapture] -> Either String ClosureCaptureSummary
captureSummary = mapLeft show . checkClosureCaptures

linearCapture, affineCapture :: ClosureCapture
linearCapture = ClosureCapture
  { closureCaptureOccurrence = CaptureOccurrenceKey "owned-linear"
  , closureCaptureTransfer = MoveCapture
  , closureCaptureStructuralMode = Linear
  }
affineCapture = ClosureCapture
  { closureCaptureOccurrence = CaptureOccurrenceKey "owned-affine"
  , closureCaptureTransfer = MoveCapture
  , closureCaptureStructuralMode = Affine
  }

contract :: CallableContract
contract = CallableContract
  { callableContractInterfaceRevision = contractRevision
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.empty
  }

contractRevision :: InterfaceRevision
contractRevision = InterfaceRevision "callable.mode.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
