{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.DataSubjectTransport
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-012 same semantic subject preserves evidence without transport" sameSubjectPreserves
    , test "DATA-012 replacement subject without transport rejects" replacementWithoutTransportRejects
    , test "DATA-012 exact accepted succession transport retargets evidence" exactSuccessionAccepts
    , test "DATA-012 same stable-id kind is insufficient" sameKindIsInsufficient
    , test "DATA-012 same representation token is insufficient" sameRepresentationIsInsufficient
    , test "DATA-012 wrong prior subject in transport rejects" wrongPriorTransportRejects
    , test "DATA-012 wrong replacement subject in transport rejects" wrongReplacementTransportRejects
    , test "DATA-012 wrong evidence reference in transport rejects" wrongEvidenceReferenceRejects
    , test "DATA-012 wrong source proposition in transport rejects" wrongSourcePropositionRejects
    , test "DATA-012 wrong target proposition in transport rejects" wrongTargetPropositionRejects
    , test "DATA-012 rejected succession evidence rejects" rejectedTransportRejects
    , test "DATA-012 transport requires nonempty validity revision" emptyRelationRevisionRejects
    , test "DATA-012 update must consume predecessor" predecessorMustBeConsumed
    , test "DATA-012 update must construct replacement" replacementMustBeConstructed
    , test "DATA-012 evidence must already bind predecessor subject" evidenceMustBindPredecessor
    , test "DATA-012 stable subject kinds cannot silently change" subjectKindMismatchRejects
    , test "DATA-012 non-stable subject identity rejects" nonStableSubjectRejects
    , test "DATA-012 subject-bound evidence template must mention subject" templateMustMentionSubject
    , test "DATA-012 same subject rejects spurious transport" sameSubjectRejectsSpuriousTransport
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

sameSubjectPreserves :: Either String ()
sameSubjectPreserves = do
  let sameReplacement = priorSubject
        { dataSubjectRepresentationToken = Just "object-slot:new-generation" }
      sameUpdate = update
        { dataSubjectUpdateReplacement = sameReplacement }
  checked <- mapLeft show $ checkDataSubjectEvidenceUpdate sameUpdate evidence Nothing
  assert
    (subjectEvidenceProposition (checkedDataSubjectResultEvidence checked) ==
      subjectEvidenceProposition evidence)
    "same semantic subject changed the proposition"
  assert
    (dataSubjectIdentity (subjectEvidenceSubject (checkedDataSubjectResultEvidence checked)) ==
      dataSubjectIdentity priorSubject)
    "same semantic subject changed identity"

replacementWithoutTransportRejects :: Either String ()
replacementWithoutTransportRejects =
  expectError isRequired (checkDataSubjectEvidenceUpdate update evidence Nothing)
  where
    isRequired err = case err of
      DataSubjectTransportRequired expectedPrior expectedReplacement ->
        expectedPrior == dataSubjectIdentity priorSubject &&
        expectedReplacement == dataSubjectIdentity replacementSubject
      _ -> False

exactSuccessionAccepts :: Either String ()
exactSuccessionAccepts = do
  checked <- mapLeft show $
    checkDataSubjectEvidenceUpdate update evidence (Just validTransport)
  let result = checkedDataSubjectResultEvidence checked
  assert (subjectEvidenceProposition result == replacementProposition)
    "accepted transport did not retarget exact proposition"
  assert (subjectEvidenceReference result == subjectEvidenceReference evidence)
    "accepted transport changed evidence identity"

sameKindIsInsufficient :: Either String ()
sameKindIsInsufficient = replacementWithoutTransportRejects

sameRepresentationIsInsufficient :: Either String ()
sameRepresentationIsInsufficient = do
  let representedPrior = priorSubject
        { dataSubjectRepresentationToken = Just "ptr:shared" }
      representedReplacement = replacementSubject
        { dataSubjectRepresentationToken = Just "ptr:shared" }
      representedUpdate = update
        { dataSubjectUpdatePrior = representedPrior
        , dataSubjectUpdateReplacement = representedReplacement
        }
      representedEvidence = evidence
        { subjectEvidenceSubject = representedPrior }
  expectError isRequired $
    checkDataSubjectEvidenceUpdate representedUpdate representedEvidence Nothing
  where
    isRequired err = case err of
      DataSubjectTransportRequired _ _ -> True
      _ -> False

wrongPriorTransportRejects :: Either String ()
wrongPriorTransportRejects =
  expectError isWrong $ checkDataSubjectEvidenceUpdate update evidence $ Just
    validTransport { dataSubjectTransportPriorIdentity = unrelatedSubjectIdentity }
  where
    isWrong err = case err of
      DataSubjectTransportPriorMismatch _ actual -> actual == unrelatedSubjectIdentity
      _ -> False

wrongReplacementTransportRejects :: Either String ()
wrongReplacementTransportRejects =
  expectError isWrong $ checkDataSubjectEvidenceUpdate update evidence $ Just
    validTransport { dataSubjectTransportReplacementIdentity = unrelatedSubjectIdentity }
  where
    isWrong err = case err of
      DataSubjectTransportReplacementMismatch _ actual -> actual == unrelatedSubjectIdentity
      _ -> False

wrongEvidenceReferenceRejects :: Either String ()
wrongEvidenceReferenceRejects =
  expectError isWrong $ checkDataSubjectEvidenceUpdate update evidence $ Just
    validTransport { dataSubjectTransportEvidenceReference = "proof:other" }
  where
    isWrong err = case err of
      DataSubjectTransportEvidenceMismatch expected actual ->
        expected == subjectEvidenceReference evidence && actual == "proof:other"
      _ -> False

wrongSourcePropositionRejects :: Either String ()
wrongSourcePropositionRejects =
  expectError isWrong $ checkDataSubjectEvidenceUpdate update evidence $ Just
    validTransport { dataSubjectTransportSourceProposition = Truth }
  where
    isWrong err = case err of
      DataSubjectTransportSourcePropositionMismatch expected actual ->
        expected == priorProposition && actual == Truth
      _ -> False

wrongTargetPropositionRejects :: Either String ()
wrongTargetPropositionRejects =
  expectError isWrong $ checkDataSubjectEvidenceUpdate update evidence $ Just
    validTransport { dataSubjectTransportTargetProposition = Truth }
  where
    isWrong err = case err of
      DataSubjectTransportTargetPropositionMismatch expected actual ->
        expected == replacementProposition && actual == Truth
      _ -> False

rejectedTransportRejects :: Either String ()
rejectedTransportRejects =
  expectError isRejected $ checkDataSubjectEvidenceUpdate update evidence $ Just
    validTransport { dataSubjectTransportDisposition = SubjectTransportRejected "not-established" }
  where
    isRejected err = case err of
      DataSubjectTransportRejected reason -> reason == "not-established"
      _ -> False

emptyRelationRevisionRejects :: Either String ()
emptyRelationRevisionRejects =
  expectError (== DataSubjectTransportRelationRevisionMissing) $
    checkDataSubjectEvidenceUpdate update evidence $ Just
      validTransport { dataSubjectTransportRelationRevision = "" }

predecessorMustBeConsumed :: Either String ()
predecessorMustBeConsumed =
  expectError (== DataSubjectPriorNotConsumed) $
    checkDataSubjectEvidenceUpdate
      update { dataSubjectUpdatePriorConsumed = False }
      evidence
      (Just validTransport)

replacementMustBeConstructed :: Either String ()
replacementMustBeConstructed =
  expectError (== DataSubjectReplacementNotConstructed) $
    checkDataSubjectEvidenceUpdate
      update { dataSubjectUpdateReplacementConstructed = False }
      evidence
      (Just validTransport)

evidenceMustBindPredecessor :: Either String ()
evidenceMustBindPredecessor =
  expectError isWrong $
    checkDataSubjectEvidenceUpdate update
      evidence { subjectEvidenceSubject = unrelatedSubject }
      (Just validTransport)
  where
    isWrong err = case err of
      DataSubjectEvidencePriorMismatch expected actual ->
        expected == dataSubjectIdentity priorSubject && actual == unrelatedSubjectIdentity
      _ -> False

subjectKindMismatchRejects :: Either String ()
subjectKindMismatchRejects = do
  let otherKind = DataSubject
        (RefOpaque (SortStableId "different-kind") "subject:k2")
        (Just "ptr:same")
      otherUpdate = update { dataSubjectUpdateReplacement = otherKind }
  expectError isMismatch $
    checkDataSubjectEvidenceUpdate otherUpdate evidence Nothing
  where
    isMismatch err = case err of
      DataSubjectKindMismatch priorKind replacementKind ->
        priorKind == "provider-evidence-subject" && replacementKind == "different-kind"
      _ -> False

nonStableSubjectRejects :: Either String ()
nonStableSubjectRejects = do
  let nonStable = DataSubject (RefOpaque SortNat "not-stable") Nothing
      badUpdate = update { dataSubjectUpdatePrior = nonStable }
      badEvidence = evidence { subjectEvidenceSubject = nonStable }
  expectError isNonStable $
    checkDataSubjectEvidenceUpdate badUpdate badEvidence Nothing
  where
    isNonStable err = case err of
      DataSubjectNotStableIdentity (RefOpaque SortNat "not-stable") -> True
      _ -> False

templateMustMentionSubject :: Either String ()
templateMustMentionSubject = do
  let independent = evidence
        { subjectEvidenceTemplate = Atom "GlobalFact" [contentId] }
  expectError isMissing $
    checkDataSubjectEvidenceUpdate update independent (Just validTransport)
  where
    isMissing err = case err of
      DataSubjectEvidenceTemplateDoesNotMentionSubject actual -> actual == subjectBinder
      _ -> False

sameSubjectRejectsSpuriousTransport :: Either String ()
sameSubjectRejectsSpuriousTransport = do
  let sameUpdate = update { dataSubjectUpdateReplacement = priorSubject }
      sameTransport = validTransport
        { dataSubjectTransportReplacementIdentity = dataSubjectIdentity priorSubject
        , dataSubjectTransportTargetProposition = priorProposition
        }
  expectError (== DataSubjectUnexpectedTransportForSameSubject) $
    checkDataSubjectEvidenceUpdate sameUpdate evidence (Just sameTransport)

expectError
  :: (DataSubjectTransportError -> Bool)
  -> Either DataSubjectTransportError a
  -> Either String ()
expectError predicate result = case result of
  Left err
    | predicate err -> Right ()
    | otherwise -> Left ("wrong error: " <> show err)
  Right _ -> Left "unexpected acceptance"

subjectBinder :: Name
subjectBinder = Name "object"

contentId :: RefTerm
contentId = RefOpaque (SortStableId "content-id:sha256") "id:example"

priorSubjectIdentity, replacementSubjectIdentity, unrelatedSubjectIdentity :: RefTerm
priorSubjectIdentity =
  RefOpaque (SortStableId "provider-evidence-subject") "object:k1"
replacementSubjectIdentity =
  RefOpaque (SortStableId "provider-evidence-subject") "object:k2"
unrelatedSubjectIdentity =
  RefOpaque (SortStableId "provider-evidence-subject") "object:k3"

priorSubject, replacementSubject, unrelatedSubject :: DataSubject
priorSubject = DataSubject priorSubjectIdentity (Just "ptr:prior")
replacementSubject = DataSubject replacementSubjectIdentity (Just "ptr:replacement")
unrelatedSubject = DataSubject unrelatedSubjectIdentity Nothing

evidence :: SubjectBoundEvidence
evidence = SubjectBoundEvidence
  { subjectEvidenceReference = "proof:digest:k1"
  , subjectEvidenceBinder = subjectBinder
  , subjectEvidenceTemplate = Atom "DigestMatches" [contentId, RefVar subjectBinder]
  , subjectEvidenceSubject = priorSubject
  }

update :: DataSubjectUpdate
update = DataSubjectUpdate
  { dataSubjectUpdatePrior = priorSubject
  , dataSubjectUpdateReplacement = replacementSubject
  , dataSubjectUpdatePriorConsumed = True
  , dataSubjectUpdateReplacementConstructed = True
  }

priorProposition, replacementProposition :: Proposition
priorProposition = subjectEvidenceProposition evidence
replacementProposition = subjectEvidenceProposition
  evidence { subjectEvidenceSubject = replacementSubject }

validTransport :: DataSubjectTransport
validTransport = DataSubjectTransport
  { dataSubjectTransportKind = SubjectSuccessionTransport
  , dataSubjectTransportRelationRevision = "subject-succession:copy-verified:v1"
  , dataSubjectTransportEvidenceReference = subjectEvidenceReference evidence
  , dataSubjectTransportPriorIdentity = priorSubjectIdentity
  , dataSubjectTransportReplacementIdentity = replacementSubjectIdentity
  , dataSubjectTransportSourceProposition = priorProposition
  , dataSubjectTransportTargetProposition = replacementProposition
  , dataSubjectTransportDisposition = SubjectTransportAccepted
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
