{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Examples.Phase1.SubjectWitnesses
import Phil.Systems.IR
import Phil.Systems.Phase1Stage
import Phil.Systems.SubjectCorrespondence
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-004 upload subject correspondence accepts" uploadAccepted
    , test "SYS-004 Steve subject correspondence accepts" steveAccepted
    , test "SYS-004 equal storage identity does not merge source subjects" equalStorageStillDistinct
    , test "SYS-004 correspondence cannot be inherited by equal-storage subject" equalStorageInheritanceRejected
    , test "SYS-004 runtime representation coincidence is not a subject relation" runtimeCoincidenceRejected
    , test "SYS-004 unknown Systems value rejects" unknownValueRejected
    , test "SYS-004 one Systems value cannot bind two stable subjects" sharedValueRejected
    , test "SYS-004 subject-stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadAccepted :: Either String ()
uploadAccepted = mapLeft show $ verifySubjectStageBundle uploadSubjectStageBundle

steveAccepted :: Either String ()
steveAccepted = steveBundle >>= mapLeft show . verifySubjectStageBundle

equalStorageStillDistinct :: Either String ()
equalStorageStillDistinct = do
  original <- steveBundle
  mutatedBase <- withReadStorageIdentity "steve.candidate" (subjectStageBase original)
  mapLeft show $ verifySubjectStageBundle
    (makeSubjectStageBundle mutatedBase (subjectStageCorrespondences original))

equalStorageInheritanceRejected :: Either String ()
equalStorageInheritanceRejected = do
  original <- steveBundle
  mutatedBase <- withReadStorageIdentity "steve.candidate" (subjectStageBase original)
  candidate <- lookupCorrespondence steveCandidateSubject original
  let readOwner = SystemsValueRef "SteveGet" (ValueId "get.bytes")
      stolen = candidate { subjectCorrespondenceSystemsValues = Set.singleton readOwner }
      correspondences = Map.insert steveCandidateSubject stolen
        (subjectStageCorrespondences original)
      mutated = makeSubjectStageBundle mutatedBase correspondences
  case verifySubjectStageBundle mutated of
    Left (SubjectCorrespondenceSystemsValueShared ref subjects) -> do
      assert (ref == readOwner) "wrong shared Systems value diagnostic"
      assert (subjects == Set.fromList [steveCandidateSubject, steveReadSubject])
        "wrong source subjects in shared-value diagnostic"
    other -> Left ("equal-storage correspondence inheritance was accepted: " <> show other)

runtimeCoincidenceRejected :: Either String ()
runtimeCoincidenceRejected = do
  original <- steveBundle
  candidate <- lookupCorrespondence steveCandidateSubject original
  let bad = candidate
        { subjectCorrespondenceBasis =
            RuntimeRepresentationCoincidence "same pointer/storage/bytes" }
      mutated = makeSubjectStageBundle (subjectStageBase original)
        (Map.insert steveCandidateSubject bad (subjectStageCorrespondences original))
  case verifySubjectStageBundle mutated of
    Left (SubjectCorrespondenceRuntimeCoincidenceRejected subject _) ->
      assert (subject == steveCandidateSubject) "wrong coincidence subject"
    other -> Left ("runtime coincidence was accepted as semantic identity: " <> show other)

unknownValueRejected :: Either String ()
unknownValueRejected = do
  original <- steveBundle
  candidate <- lookupCorrespondence steveCandidateSubject original
  let missing = SystemsValueRef "StevePut" (ValueId "put.not-a-value")
      bad = candidate { subjectCorrespondenceSystemsValues = Set.singleton missing }
      mutated = makeSubjectStageBundle (subjectStageBase original)
        (Map.insert steveCandidateSubject bad (subjectStageCorrespondences original))
  case verifySubjectStageBundle mutated of
    Left (SubjectCorrespondenceUnknownValue subject actual) -> do
      assert (subject == steveCandidateSubject) "wrong unknown-value subject"
      assert (actual == missing) "wrong unknown Systems value"
    other -> Left ("unknown Systems value was accepted: " <> show other)

sharedValueRejected :: Either String ()
sharedValueRejected = do
  original <- steveBundle
  candidate <- lookupCorrespondence steveCandidateSubject original
  readResult <- lookupCorrespondence steveReadSubject original
  let shared = SystemsValueRef "StevePut" (ValueId "put.candidate")
      candidate' = candidate { subjectCorrespondenceSystemsValues = Set.singleton shared }
      read' = readResult { subjectCorrespondenceSystemsValues = Set.singleton shared }
      correspondences = Map.fromList
        [ (steveCandidateSubject, candidate')
        , (steveReadSubject, read')
        ]
      mutated = makeSubjectStageBundle (subjectStageBase original) correspondences
  case verifySubjectStageBundle mutated of
    Left (SubjectCorrespondenceSystemsValueShared actual _) ->
      assert (actual == shared) "wrong shared-value diagnostic"
    other -> Left ("one Systems value was accepted for two stable subjects: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- steveBundle
  let reversed = Map.fromList (reverse (Map.toAscList (subjectStageCorrespondences original)))
      rebuilt = makeSubjectStageBundle (subjectStageBase original) reversed
  assert (subjectStageRevision rebuilt == subjectStageRevision original)
    "subject-stage revision changed with map enumeration order"
  mapLeft show $ verifySubjectStageBundle rebuilt

withReadStorageIdentity :: Text -> Phase1StageBundle -> Either String Phase1StageBundle
withReadStorageIdentity storage base = do
  let artifact = phase1StageSystemsArtifact base
      program = systemsArtifactProgram artifact
  getFunction <- maybe (Left "SteveGet missing") Right
    (Map.lookup "SteveGet" (systemsProgramFunctions program))
  getBytes <- maybe (Left "get.bytes missing") Right
    (Map.lookup (ValueId "get.bytes") (systemsFunctionValues getFunction))
  let changedValue = getBytes { systemsStorageIdentity = Just storage }
      changedFunction = getFunction
        { systemsFunctionValues = Map.insert (ValueId "get.bytes") changedValue
            (systemsFunctionValues getFunction) }
      changedProgram = program
        { systemsProgramFunctions = Map.insert "SteveGet" changedFunction
            (systemsProgramFunctions program) }
      oldContract = systemsArtifactStageContract artifact
      changedContract = oldContract
        { stageTargetArtifactDigest = systemsProgramDigest changedProgram }
      changedArtifact = artifact
        { systemsArtifactProgram = changedProgram
        , systemsArtifactStageContract = changedContract }
  pure (makePhase1StageBundle
    (phase1StageInstanceRevision base)
    (phase1StageRealizationRevision base)
    (phase1StageVerifierProfileRevision base)
    changedArtifact
    (phase1StageFactDispositions base)
    (phase1StageSystemsJustifications base))

lookupCorrespondence
  :: SourceSubjectKey
  -> SubjectStageBundle
  -> Either String SubjectCorrespondence
lookupCorrespondence key bundle = maybe
  (Left ("missing correspondence: " <> show key))
  Right
  (Map.lookup key (subjectStageCorrespondences bundle))

steveBundle :: Either String SubjectStageBundle
steveBundle = steveSubjectStageBundle

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
