{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
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
    , test "SYS-004 unknown Systems function rejects" unknownFunctionRejected
    , test "SYS-004 one Systems value cannot bind two stable subjects" sharedValueRejected
    , test "SYS-004 correspondence map key must equal semantic subject" keyMismatchRejected
    , test "SYS-004 subject relation revision must be nonempty" emptyRelationRejected
    , test "SYS-004 validity scope must be nonempty" emptyValidityRejected
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

-- Two distinct owned values may happen to carry the same concrete storage hint.
-- Subject correspondence is still keyed by exact SystemsValueRef, not by storage.
equalStorageStillDistinct :: Either String ()
equalStorageStillDistinct = do
  original <- steveBundle
  mutatedBase <- withReadStorageIdentity "steve.candidate" (subjectStageBase original)
  let mutated = makeSubjectStageBundle mutatedBase (subjectStageCorrespondences original)
  mapLeft show $ verifySubjectStageBundle mutated

-- Even after forcing the two owners to share a concrete storage hint, the
-- candidate subject may not steal the read-result subject's exact Systems value.
equalStorageInheritanceRejected :: Either String ()
equalStorageInheritanceRejected = do
  original <- steveBundle
  mutatedBase <- withReadStorageIdentity "steve.candidate" (subjectStageBase original)
  candidate <- lookupCorrespondence steveCandidateSubject original
  let readOwner = SystemsValueRef "SteveGet" (ValueId "get.bytes")
      stolen = candidate
        { subjectCorrespondenceSystemsValues = Set.singleton readOwner }
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

unknownFunctionRejected :: Either String ()
unknownFunctionRejected = do
  original <- steveBundle
  candidate <- lookupCorrespondence steveCandidateSubject original
  let missing = SystemsValueRef "SteveElsewhere" (ValueId "put.candidate")
      bad = candidate { subjectCorrespondenceSystemsValues = Set.singleton missing }
      mutated = makeSubjectStageBundle (subjectStageBase original)
        (Map.insert steveCandidateSubject bad (subjectStageCorrespondences original))
  case verifySubjectStageBundle mutated of
    Left (SubjectCorrespondenceUnknownFunction subject functionName) -> do
      assert (subject == steveCandidateSubject) "wrong unknown-function subject"
      assert (functionName == "SteveElsewhere") "wrong unknown function"
    other -> Left ("unknown Systems function was accepted: " <> show other)

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

keyMismatchRejected :: Either String ()
keyMismatchRejected = do
  original <- steveBundle
  candidate <- lookupCorrespondence steveCandidateSubject original
  let bad = candidate { subjectCorrespondenceSource = SourceSubjectKey "wrong.subject" }
      mutated = makeSubjectStageBundle (subjectStageBase original)
        (Map.insert steveCandidateSubject bad (subjectStageCorrespondences original))
  case verifySubjectStageBundle mutated of
    Left (SubjectCorrespondenceMapKeyMismatch expected actual) -> do
      assert (expected == steveCandidateSubject) "wrong expected subject key"
      assert (actual == SourceSubjectKey "wrong.subject") "wrong actual subject key"
    other -> Left ("subject-key mismatch was accepted: " <> show other)

emptyRelationRejected :: Either String ()
emptyRelationRejected = do
  original <- steveBundle
  candidate <- lookupCorrespondence steveCandidateSubject original
  let bad = candidate
        { subjectCorrespondenceBasis = CheckedSubjectRelation (SubjectRelationRevision "") }
      mutated = makeSubjectStageBundle (subjectStageBase original)
        (Map.insert steveCandidateSubject bad (subjectStageCorrespondences original))
  case verifySubjectStageBundle mutated of
    Left (SubjectCorrespondenceEmptyRelationRevision subject) ->
      assert (subject == steveCandidateSubject) "wrong empty-relation subject"
    other -> Left ("empty subject relation was accepted: " <> show other)

emptyValidityRejected :: Either String ()
emptyValidityRejected = do
  original <- steveBundle
  candidate <- lookupCorrespondence steveCandidateSubject original
  let bad = candidate
        { subjectCorrespondenceValidityScope = SubjectValidityScopeRevision "" }
      mutated = makeSubjectStageBundle (subjectStageBase original)
        (Map.insert steveCandidateSubject bad (subjectStageCorrespondences original))
  case verifySubjectStageBundle mutated of
    Left (SubjectCorrespondenceEmptyValidityScope subject) ->
      assert (subject == steveCandidateSubject) "wrong empty-validity subject"
    other -> Left ("empty subject validity scope was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- steveBundle
  let reversed = Map.fromList (reverse (Map.toAscList (subjectStageCorrespondences original)))
      rebuilt = makeSubjectStageBundle (subjectStageBase original) reversed
  assert (subjectStageRevision rebuilt == subjectStageRevision original)
    "subject-stage revision changed with map enumeration order"
  mapLeft show $ verifySubjectStageBundle rebuilt

withReadStorageIdentity :: String -> Phase1StageBundle -> Either String Phase1StageBundle
withReadStorageIdentity storage base = do
  let artifact = phase1StageSystemsArtifact base
      program = systemsArtifactProgram artifact
  getFunction <- maybe (Left "SteveGet missing") Right
    (Map.lookup "SteveGet" (systemsProgramFunctions program))
  getBytes <- maybe (Left "get.bytes missing") Right
    (Map.lookup (ValueId "get.bytes") (systemsFunctionValues getFunction))
  let changedValue = getBytes { systemsStorageIdentity = Just (fromString storage) }
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

fromString :: String -> Data.Text.Text
fromString = Data.Text.pack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
