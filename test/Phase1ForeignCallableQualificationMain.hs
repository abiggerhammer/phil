{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.CallableQualification
import Phil.Core.CallableRefinement
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Outcome (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-015 matching signature without qualification rejects" signatureOnlyRejects
    , test "CALL-015 ABI evidence alone is insufficient" abiOnlyRejects
    , test "CALL-015 complete explicit qualification accepts" completeQualificationAccepts
    , test "CALL-015 qualification is bound to exact foreign artifact" wrongArtifactRejects
    , test "CALL-015 qualification surface must match admitted artifact facts" surfaceMismatchRejects
    , test "CALL-015 complete evidence does not excuse wider effects" qualifiedWiderEffectsReject
    , test "CALL-015 complete evidence does not excuse stronger authority" qualifiedStrongerAuthorityReject
    , test "CALL-015 complete evidence does not excuse fatal behavior" qualifiedFatalBehaviorReject
    , test "CALL-015 missing-evidence diagnostic is canonical" missingEvidenceCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

signatureOnlyRejects :: Either String ()
signatureOnlyRejects =
  case checkForeignCallableQualification expectedSurface matchingArtifact Nothing of
    Left (ForeignCallableQualificationMissing key) ->
      assert (key == matchingArtifactKey) "missing-qualification diagnostic named wrong artifact"
    other -> Left ("signature-only foreign callable did not reject: " <> show other)

abiOnlyRejects :: Either String ()
abiOnlyRejects =
  case checkForeignCallableQualification expectedSurface matchingArtifact
      (Just matchingQualification { foreignQualificationEvidence = abiOnlyEvidence }) of
    Left (ForeignCallableQualificationMissingEvidence missing) ->
      assert
        (missing == Set.delete ForeignCallableAbiCorrespondence requiredForeignCallableEvidence)
        "ABI-only qualification did not report every remaining semantic evidence dimension"
    other -> Left ("ABI-only qualification did not reject: " <> show other)

completeQualificationAccepts :: Either String ()
completeQualificationAccepts = do
  checked <- mapLeft show $ checkForeignCallableQualification
    expectedSurface matchingArtifact (Just matchingQualification)
  assert
    (foreignCallableArtifactKey (checkedForeignArtifact checked) == matchingArtifactKey)
    "accepted qualification changed artifact identity"
  assert
    (foreignQualificationEvidence (checkedForeignQualification checked) == completeEvidence)
    "accepted qualification changed evidence record"

wrongArtifactRejects :: Either String ()
wrongArtifactRejects =
  let reused = matchingQualification
        { foreignQualificationArtifactKey = otherArtifactKey }
  in case checkForeignCallableQualification expectedSurface matchingArtifact (Just reused) of
    Left (ForeignCallableQualificationArtifactMismatch actual qualified) -> do
      assert (actual == matchingArtifactKey) "wrong-artifact diagnostic lost actual artifact"
      assert (qualified == otherArtifactKey) "wrong-artifact diagnostic lost qualification target"
    other -> Left ("qualification for another artifact was reused: " <> show other)

surfaceMismatchRejects :: Either String ()
surfaceMismatchRejects =
  let inconsistent = matchingQualification
        { foreignQualificationSurface = widerEffectSurface }
  in case checkForeignCallableQualification expectedSurface matchingArtifact (Just inconsistent) of
    Left (ForeignCallableQualificationSurfaceMismatch observed qualified) -> do
      assert (observed == matchingSurface) "surface mismatch lost observed artifact facts"
      assert (qualified == widerEffectSurface) "surface mismatch lost qualified facts"
    other -> Left ("qualification surface mismatch was accepted: " <> show other)

qualifiedWiderEffectsReject :: Either String ()
qualifiedWiderEffectsReject =
  case checkForeignCallableQualification expectedSurface widerEffectArtifact
      (Just widerEffectQualification) of
    Left (ForeignCallableQualificationRefinementError (CallableEffectBoundTooWide excess)) ->
      assert (excess == Set.singleton writeEffect)
        "wider-effect qualification reported wrong excess effect"
    other -> Left ("qualified wider-effect callable did not reject: " <> show other)

qualifiedStrongerAuthorityReject :: Either String ()
qualifiedStrongerAuthorityReject =
  case checkForeignCallableQualification expectedSurface strongerAuthorityArtifact
      (Just strongerAuthorityQualification) of
    Left (ForeignCallableQualificationRefinementError
        (CallableAuthorityRequirementTooStrong excess)) ->
      assert (excess == Set.singleton deleteAuthority)
        "stronger-authority qualification reported wrong excess authority"
    other -> Left ("qualified stronger-authority callable did not reject: " <> show other)

qualifiedFatalBehaviorReject :: Either String ()
qualifiedFatalBehaviorReject =
  case checkForeignCallableQualification expectedSurface fatalArtifact
      (Just fatalQualification) of
    Left (ForeignCallableQualificationRefinementError (CallableFailureSetTooWide excess)) ->
      assert (excess == Set.singleton (CallableFatal "abort"))
        "fatal-behavior qualification reported wrong excess failure"
    other -> Left ("qualified fatal callable did not reject: " <> show other)

missingEvidenceCanonical :: Either String ()
missingEvidenceCanonical =
  let leftEvidence = Map.fromList
        [ (ForeignCallableAbiCorrespondence, "abi-cert")
        , (ForeignCallableEffectConfinement, "effect-cert")
        ]
      rightEvidence = Map.fromList
        [ (ForeignCallableEffectConfinement, "effect-cert")
        , (ForeignCallableAbiCorrespondence, "abi-cert")
        ]
      check evidence = checkForeignCallableQualification expectedSurface matchingArtifact
        (Just matchingQualification { foreignQualificationEvidence = evidence })
  in assert (check leftEvidence == check rightEvidence)
      "evidence enumeration order changed qualification result"

matchingArtifactKey, otherArtifactKey, widerEffectArtifactKey,
  strongerAuthorityArtifactKey, fatalArtifactKey :: ForeignCallableArtifactKey
matchingArtifactKey = ForeignCallableArtifactKey "foreign.read.impl.001"
otherArtifactKey = ForeignCallableArtifactKey "foreign.read.impl.002"
widerEffectArtifactKey = ForeignCallableArtifactKey "foreign.readwrite.impl.001"
strongerAuthorityArtifactKey = ForeignCallableArtifactKey "foreign.delete.impl.001"
fatalArtifactKey = ForeignCallableArtifactKey "foreign.abort.impl.001"

shape :: CallableMachineShape
shape = CallableMachineShape "fn(bytes)->status"

readAuthority, deleteAuthority :: CallableAuthorityRequirement
readAuthority = CallableAuthorityRequirement "storage.read"
deleteAuthority = CallableAuthorityRequirement "storage.delete"

readEffect, writeEffect :: SemanticEffect
readEffect = SemanticEffect "read"
writeEffect = SemanticEffect "write"

notFound :: CallableFailure
notFound = CallableTypedNegative (Outcome "not-found")

expectedSurface, matchingSurface, widerEffectSurface,
  strongerAuthoritySurface, fatalSurface :: CallableRefinementSurface
expectedSurface = CallableRefinementSurface
  { callableRefinementMachineShape = shape
  , callableRefinementContract = CallableContract
      (InterfaceRevision "callable.storage-read.v1")
      PreserveCallee
      (Set.singleton readEffect)
  , callableRefinementCallerAuthority = Set.singleton readAuthority
  , callableRefinementFailures = Set.singleton notFound
  }

matchingSurface = expectedSurface
  { callableRefinementContract = CallableContract
      (InterfaceRevision "foreign.storage-read.impl.v7")
      PreserveCallee
      (Set.singleton readEffect)
  }

widerEffectSurface = matchingSurface
  { callableRefinementContract = CallableContract
      (InterfaceRevision "foreign.storage-readwrite.impl.v1")
      PreserveCallee
      (Set.fromList [readEffect, writeEffect])
  }

strongerAuthoritySurface = matchingSurface
  { callableRefinementCallerAuthority = Set.fromList [readAuthority, deleteAuthority] }

fatalSurface = matchingSurface
  { callableRefinementFailures = Set.fromList [notFound, CallableFatal "abort"] }

matchingArtifact, widerEffectArtifact, strongerAuthorityArtifact, fatalArtifact
  :: ForeignCallableArtifact
matchingArtifact = ForeignCallableArtifact matchingArtifactKey matchingSurface
widerEffectArtifact = ForeignCallableArtifact widerEffectArtifactKey widerEffectSurface
strongerAuthorityArtifact = ForeignCallableArtifact
  strongerAuthorityArtifactKey strongerAuthoritySurface
fatalArtifact = ForeignCallableArtifact fatalArtifactKey fatalSurface

completeEvidence :: Map.Map ForeignCallableEvidenceKind String
completeEvidence = error "completeEvidence text-specialized below"

-- Keep evidence values as Text while retaining a compact fixture declaration.
completeEvidenceText :: Map.Map ForeignCallableEvidenceKind Data.Text.Text
completeEvidenceText = Map.fromList
  [ (ForeignCallableAbiCorrespondence, "abi-cert")
  , (ForeignCallableResourceLifecycle, "resource-cert")
  , (ForeignCallableEffectConfinement, "effect-cert")
  , (ForeignCallableAuthorityConfinement, "authority-cert")
  , (ForeignCallableFailureBehavior, "failure-cert")
  ]

abiOnlyEvidence :: Map.Map ForeignCallableEvidenceKind Data.Text.Text
abiOnlyEvidence = Map.singleton ForeignCallableAbiCorrespondence "abi-cert"

matchingQualification, widerEffectQualification,
  strongerAuthorityQualification, fatalQualification :: ForeignCallableQualification
matchingQualification = ForeignCallableQualification
  matchingArtifactKey matchingSurface completeEvidenceText
widerEffectQualification = ForeignCallableQualification
  widerEffectArtifactKey widerEffectSurface completeEvidenceText
strongerAuthorityQualification = ForeignCallableQualification
  strongerAuthorityArtifactKey strongerAuthoritySurface completeEvidenceText
fatalQualification = ForeignCallableQualification
  fatalArtifactKey fatalSurface completeEvidenceText

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
