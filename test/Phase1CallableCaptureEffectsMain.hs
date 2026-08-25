{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-001 no restricted captures yield unrestricted closure" noCaptureClosureIsUnrestricted
    , test "CALL-001 PreserveCallee remains explicit in callable contract" preserveCalleeIsExplicit
    , test "CALL-002 linear capture moves ownership into closure" linearCaptureMovesOwnership
    , test "CALL-002 affine capture raises closure mode to affine" affineCaptureRaisesMode
    , test "CALL-002 linear capture dominates mixed closure mode" linearCaptureDominatesMode
    , test "CALL-003 restricted capture cannot be copied" restrictedCaptureCannotCopy
    , test "CALL-003 restricted occurrence cannot be captured twice" duplicateRestrictedCaptureRejects
    , test "capture summary is canonical under enumeration order" captureOrderingIsCanonical
    , test "CALL-004 possessing callable does not propagate invocation effects" possessionDoesNotPropagateEffects
    , test "CALL-004 forwarding storing and returning callable stay effect-neutral" forwardingDoesNotPropagateEffects
    , test "CALL-005 reachable invocation propagates exact public effect bound" invocationPropagatesEffects
    , test "CALL-005 repeated invocation effect inference is canonical set union" invocationEffectsAreCanonicalUnion
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

noCaptureClosureIsUnrestricted :: Either String ()
noCaptureClosureIsUnrestricted = do
  summary <- mapLeft show (checkClosureCaptures [])
  assert
    (closureMinimumStructuralMode summary == Unrestricted)
    "empty closure did not have unrestricted minimum mode"

preserveCalleeIsExplicit :: Either String ()
preserveCalleeIsExplicit =
  assert
    (callableContractCalleeTransition pureContract == PreserveCallee)
    "ordinary callable contract did not preserve callee"

linearCaptureMovesOwnership :: Either String ()
linearCaptureMovesOwnership = do
  summary <- mapLeft show (checkClosureCaptures [linearCapture])
  assert
    (closureMinimumStructuralMode summary == Linear)
    "linear capture did not make closure linear"
  assert
    (Set.member ownerOccurrence (closureMovedRestrictedOccurrences summary))
    "moved linear predecessor was not recorded as transferred"

affineCaptureRaisesMode :: Either String ()
affineCaptureRaisesMode = do
  summary <- mapLeft show (checkClosureCaptures [affineCapture])
  assert
    (closureMinimumStructuralMode summary == Affine)
    "affine capture did not make closure affine"

linearCaptureDominatesMode :: Either String ()
linearCaptureDominatesMode = do
  summary <- mapLeft show
    (checkClosureCaptures [unrestrictedCapture, affineCapture, linearCapture])
  assert
    (closureMinimumStructuralMode summary == Linear)
    "linear capture did not dominate mixed closure structural mode"

restrictedCaptureCannotCopy :: Either String ()
restrictedCaptureCannotCopy =
  case checkClosureCaptures
      [ClosureCapture ownerOccurrence CopyCapture Linear] of
    Left (RestrictedCaptureMustMove key mode) -> do
      assert (key == ownerOccurrence) "copy diagnostic named wrong occurrence"
      assert (mode == Linear) "copy diagnostic named wrong mode"
    other -> Left ("restricted copy did not reject: " <> show other)

duplicateRestrictedCaptureRejects :: Either String ()
duplicateRestrictedCaptureRejects =
  case checkClosureCaptures [linearCapture, linearCapture] of
    Left (DuplicateRestrictedCapture key mode) -> do
      assert (key == ownerOccurrence) "duplicate diagnostic named wrong occurrence"
      assert (mode == Linear) "duplicate diagnostic named wrong mode"
    other -> Left ("duplicate restricted capture did not reject: " <> show other)

captureOrderingIsCanonical :: Either String ()
captureOrderingIsCanonical = do
  left <- mapLeft show
    (checkClosureCaptures [unrestrictedCapture, affineCapture, linearCapture])
  right <- mapLeft show
    (checkClosureCaptures [linearCapture, unrestrictedCapture, affineCapture])
  assert (left == right) "capture enumeration order changed semantic summary"

possessionDoesNotPropagateEffects :: Either String ()
possessionDoesNotPropagateEffects =
  assert
    (Set.null (inferReachableCallableEffects [PossessCallable ioContract]))
    "mere callable possession imported invocation effects"

forwardingDoesNotPropagateEffects :: Either String ()
forwardingDoesNotPropagateEffects =
  assert
    (Set.null (inferReachableCallableEffects
      [ PassCallable ioContract
      , StoreCallable ioContract
      , ReturnCallable ioContract
      ]))
    "forwarding/storage/return imported invocation effects"

invocationPropagatesEffects :: Either String ()
invocationPropagatesEffects =
  assert
    ( inferReachableCallableEffects [InvokeCallable ioContract]
        == callableContractEffectBound ioContract )
    "reachable invocation did not import exact public effect bound"

invocationEffectsAreCanonicalUnion :: Either String ()
invocationEffectsAreCanonicalUnion =
  let expected = Set.fromList [readEffect, installEffect, auditEffect]
      actual = inferReachableCallableEffects
        [ InvokeCallable ioContract
        , PossessCallable auditContract
        , InvokeCallable auditContract
        , InvokeCallable ioContract
        ]
  in assert (actual == expected)
      "effect inference did not canonicalize repeated invocation effects as set union"

ownerOccurrence, tokenOccurrence, labelOccurrence :: CaptureOccurrenceKey
ownerOccurrence = CaptureOccurrenceKey "owner.bytes.001"
tokenOccurrence = CaptureOccurrenceKey "token.cache.001"
labelOccurrence = CaptureOccurrenceKey "label.001"

linearCapture, affineCapture, unrestrictedCapture :: ClosureCapture
linearCapture = ClosureCapture ownerOccurrence MoveCapture Linear
affineCapture = ClosureCapture tokenOccurrence MoveCapture Affine
unrestrictedCapture = ClosureCapture labelOccurrence CopyCapture Unrestricted

readEffect, installEffect, auditEffect :: SemanticEffect
readEffect = SemanticEffect "read"
installEffect = SemanticEffect "install-if-absent"
auditEffect = SemanticEffect "audit"

pureContract, ioContract, auditContract :: CallableContract
pureContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.pure.interface.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.empty
  }

ioContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.io.interface.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.fromList [readEffect, installEffect]
  }

auditContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.audit.interface.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.singleton auditEffect
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
