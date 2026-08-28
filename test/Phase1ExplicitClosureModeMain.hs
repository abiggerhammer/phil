{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.Callable.ModeDeclaration
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-017 omitted closure mode uses capture-derived minimum" omittedUsesDerivedMinimum
    , test "CALL-017 explicit equal mode needs no strengthening justification" explicitEqualModeAccepts
    , test "CALL-017 semantic lifecycle may strengthen closure mode" lifecycleStrengtheningAccepts
    , test "CALL-017 semantic authority may strengthen closure mode" authorityStrengtheningAccepts
    , test "CALL-017 explicit mode cannot weaken capture minimum" weakeningRejects
    , test "CALL-017 stricter mode requires semantic justification" missingJustificationRejects
    , test "CALL-017 stricter justification must name exact contract" wrongContractRejects
    , test "CALL-017 target implementation cannot strengthen source mode" targetReasonRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

omittedUsesDerivedMinimum :: Either String ()
omittedUsesDerivedMinimum = do
  captures <- captureSummary [linearCapture]
  checked <- mapLeft show $ checkClosureModeDeclaration contract captures DerivedClosureMode
  assert (checkedClosureMinimumMode checked == Linear)
    "linear capture did not induce linear minimum"
  assert (checkedClosureSelectedMode checked == Linear)
    "omitted mode did not select capture-derived minimum"
  assert (checkedClosureCaptureSummary checked == captures)
    "mode selection reclassified the capture environment"

explicitEqualModeAccepts :: Either String ()
explicitEqualModeAccepts = do
  captures <- captureSummary [affineCapture]
  checked <- mapLeft show $ checkClosureModeDeclaration
    contract captures (ExplicitClosureMode Affine Nothing)
  assert
    (checkedClosureMinimumMode checked == Affine
      && checkedClosureSelectedMode checked == Affine)
    "explicit mode equal to capture minimum was not preserved"

lifecycleStrengtheningAccepts :: Either String ()
lifecycleStrengtheningAccepts = do
  captures <- captureSummary []
  let justification = LifecycleModeObligation contractRevision "one-shot lifecycle"
  checked <- mapLeft show $ checkClosureModeDeclaration
    contract captures (ExplicitClosureMode Affine (Just justification))
  assert
    (checkedClosureMinimumMode checked == Unrestricted
      && checkedClosureSelectedMode checked == Affine
      && checkedClosureModeJustification checked == Just justification)
    "exact lifecycle obligation did not justify affine strengthening"
  assert (checkedClosureCaptureSummary checked == captures)
    "lifecycle strengthening rewrote capture semantics"

authorityStrengtheningAccepts :: Either String ()
authorityStrengtheningAccepts = do
  captures <- captureSummary []
  let justification = AuthorityModeObligation contractRevision "nonduplicable delegated authority"
  checked <- mapLeft show $ checkClosureModeDeclaration
    contract captures (ExplicitClosureMode Linear (Just justification))
  assert (checkedClosureSelectedMode checked == Linear)
    "exact authority obligation did not justify linear strengthening"

weakeningRejects :: Either String ()
weakeningRejects = do
  captures <- captureSummary [affineCapture]
  case checkClosureModeDeclaration
      contract captures (ExplicitClosureMode Unrestricted Nothing) of
    Left (ExplicitClosureModeWeakensCaptureMinimum Affine Unrestricted) -> Right ()
    other -> Left ("capture-derived affine minimum was weakened: " <> show other)

missingJustificationRejects :: Either String ()
missingJustificationRejects = do
  captures <- captureSummary []
  case checkClosureModeDeclaration
      contract captures (ExplicitClosureMode Linear Nothing) of
    Left (StricterClosureModeMissingSemanticJustification Unrestricted Linear) -> Right ()
    other -> Left ("unjustified stricter closure mode was accepted: " <> show other)

wrongContractRejects :: Either String ()
wrongContractRejects = do
  captures <- captureSummary []
  let wrongRevision = InterfaceRevision "callable.other.v1"
      justification = LifecycleModeObligation wrongRevision "other lifecycle"
  case checkClosureModeDeclaration
      contract captures (ExplicitClosureMode Affine (Just justification)) of
    Left (StricterClosureModeWrongContract expected actual) ->
      assert
        (expected == contractRevision && actual == wrongRevision)
        "wrong-contract mode diagnostic lost exact interface revisions"
    other -> Left ("foreign callable lifecycle justified local mode: " <> show other)

targetReasonRejects :: Either String ()
targetReasonRejects = do
  captures <- captureSummary []
  case checkClosureModeDeclaration
      contract captures
      (ExplicitClosureMode Affine
        (Just (TargetImplementationModeReason "temporary is destroyed by call instruction"))) of
    Left (TargetImplementationCannotStrengthenClosureMode detail) ->
      assert (detail == "temporary is destroyed by call instruction")
        "target-reason rejection lost implementation detail"
    other -> Left ("target implementation strengthened source closure mode: " <> show other)

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
