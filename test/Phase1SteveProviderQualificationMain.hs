{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Authority (AuthorityOperationKey (..), AuthoritySubjectKey (..))
import Phil.Core.AuthorityConfinement (AuthorityUse (..))
import Phil.Core.ProviderAuthorityQualification
import Phil.Core.ProviderEvidenceQualification
import Phil.Core.ProviderLawQualification
import Phil.Core.ProviderLifecycleQualification
import Phil.Core.ProviderQualification
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.Syntax (Proposition (..), RefSort (..), RefTerm (..))
import Phil.Examples.Steve.ProviderQualifications
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-016 both Steve providers materialize through one artifact schema" bothProvidersMaterialize
    , test "PROV-016 DigestMatches retains id parameter and stable owner subject" digestPropositionIsExact
    , test "PROV-016 digest observation is a scoped borrow, not the proof subject" digestBorrowIsObservationOnly
    , test "PROV-016 DigestProvider preserves borrowed bytes" digestBorrowResidueIsNonconsuming
    , test "PROV-016 BlobProvider install borrows candidate on every outcome" blobInstallBorrowIsNonconsuming
    , test "PROV-016 BlobProvider materializes state, law, lifecycle, and authority layers" blobWholeProviderLayersPresent
    , test "PROV-016 BlobProvider no-replace law rejects a second installed event" blobNoReplaceRejectsReplacement
    , test "PROV-016 BlobProvider lifecycle rejects partial publication" blobPartialPublicationRejected
    , test "PROV-016 broader BlobProvider authority is explicitly dispositioned" blobAuthorityExtrasAreExplicit
    , test "PROV-016 qualification evidence closes exactly the declared obligations" obligationManifestsClose
    , test "PROV-016 conditional assumptions remain explicit in admission lineage" assumptionsRemainExplicit
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

bothProvidersMaterialize :: Either String ()
bothProvidersMaterialize = do
  qs <- qualifications
  let digest = steveDigestProviderQualification qs
      blob = steveBlobProviderQualification qs
  assert (steveProviderLabel digest == "DigestProvider[SHA256]") "wrong digest label"
  assert (steveProviderLabel blob == "BlobProvider") "wrong blob label"
  assertAdmitted digest
  assertAdmitted blob

digestPropositionIsExact :: Either String ()
digestPropositionIsExact = do
  digest <- digestArtifact
  competence <- firstCompetence digest
  let expected = Atom "DigestMatches"
        [ RefOpaque (SortStableId "content-id:sha256") "role:computed-content-id"
        , RefOpaque (SortStableId "provider-evidence-subject")
            "role:steve-put-candidate-object"
        ]
  assert (checkedProviderEvidenceProposition competence == expected)
    "DigestMatches lost id parameter or stable subject"

digestBorrowIsObservationOnly :: Either String ()
digestBorrowIsObservationOnly = do
  digest <- digestArtifact
  competence <- firstCompetence digest
  case checkedProviderEvidenceObservation competence of
    ScopedBorrowEvidenceObservation _ _ -> pure ()
    other -> Left ("digest observation was not scoped borrow: " <> show other)
  assert
    (checkedProviderEvidenceSubject competence ==
      ProviderEvidenceSubjectKey "role:steve-put-candidate-object")
    "loan identity became proof subject"

digestBorrowResidueIsNonconsuming :: Either String ()
digestBorrowResidueIsNonconsuming = do
  digest <- digestArtifact
  operation <- lookupOperation "digest.compute" digest
  residue <- onlyResidue operation
  assertBorrowedNotConsumed (ProviderResourceKey "candidate-byte-view") residue

blobInstallBorrowIsNonconsuming :: Either String ()
blobInstallBorrowIsNonconsuming = do
  blob <- blobArtifact
  operation <- lookupOperation "blob.install-if-absent" blob
  let residues = Map.elems (providerOperationOutcomeResidues operation)
  assert (length residues == 3) "installIfAbsent does not expose three public outcomes"
  mapM_ (assertBorrowedNotConsumed
    (ProviderResourceKey "steve-candidate-owner-borrow")) residues

blobWholeProviderLayersPresent :: Either String ()
blobWholeProviderLayersPresent = do
  blob <- blobArtifact
  assert (steveProviderCheckedState blob /= Nothing) "missing state qualification"
  assert (not (null (steveProviderLaws blob))) "missing no-replace law"
  assert (steveProviderCheckedLifecycle blob /= Nothing) "missing lifecycle qualification"
  assert (not (Set.null (checkedProviderAuthorityExtra
    (steveProviderCheckedAuthority blob)))) "fixture did not exercise extra authority"

blobNoReplaceRejectsReplacement :: Either String ()
blobNoReplaceRejectsReplacement = do
  blob <- blobArtifact
  law <- case steveProviderLaws blob of
    (raw, _) : _ -> Right raw
    [] -> Left "missing BlobProvider law"
  let installed = ProviderImplementationEvent
        (ProviderOperationKey "blob.install-if-absent")
        (ProviderOutcomeKey "impl.blob.install.installed")
  case checkProviderLawTrace (steveProviderCheckedSemantic blob) law [installed, installed] of
    Left (ProviderLawViolation _ 1 _ _) -> Right ()
    other -> Left ("second installed event did not violate no-replace: " <> show other)

blobPartialPublicationRejected :: Either String ()
blobPartialPublicationRejected = do
  blob <- blobArtifact
  contract <- maybe (Left "missing lifecycle contract") Right
    (steveProviderLifecycleContract blob)
  model <- maybe (Left "missing lifecycle model") Right
    (steveProviderLifecycleModel blob)
  let point = ProviderLifecyclePoint
        (ProviderOperationKey "blob.install-if-absent")
        (ProviderInterruptionPointKey "install.after-publication-before-return")
      partial = ProviderInterruptionObservation
        (ProviderObservationBoundaryKey "steve.blob.client-visible-namespace.v1")
        (ProviderObservableStateKey "object.partially-committed")
        emptyResidue
        ProviderRetrySameOperation
      broken = ProviderLifecycleModel $ Map.insert point (Set.singleton partial)
        (providerLifecycleImplementationObservations model)
  case checkProviderLifecycleQualification
      (steveProviderCheckedSemantic blob) contract broken of
    Left (ProviderLifecycleForbiddenObservableState actualPoint actualState) -> do
      assert (actualPoint == point) "wrong lifecycle point rejected"
      assert (actualState == ProviderObservableStateKey "object.partially-committed")
        "wrong partial state rejected"
    other -> Left ("partial publication was accepted: " <> show other)

blobAuthorityExtrasAreExplicit :: Either String ()
blobAuthorityExtrasAreExplicit = do
  blob <- blobArtifact
  let checked = steveProviderCheckedAuthority blob
      subject = AuthoritySubjectKey "steve.blob.namespace"
      overwrite = AuthorityUse subject (AuthorityOperationKey "overwrite")
      deleteUse = AuthorityUse subject (AuthorityOperationKey "delete")
      assumption = ProviderAuthorityAssumptionKey
        "assumption:steve.blob.backing-authority-confined.v1"
      dispositions = checkedProviderAuthorityDispositions checked
  assert (checkedProviderAuthorityExtra checked == Set.fromList [overwrite, deleteUse])
    "wrong BlobProvider extra-authority set"
  assert (Map.lookup overwrite dispositions == Just (ExtraAuthorityAssumptionDependent assumption))
    "overwrite authority lacks explicit disposition"
  assert (Map.lookup deleteUse dispositions == Just (ExtraAuthorityAssumptionDependent assumption))
    "delete authority lacks explicit disposition"

obligationManifestsClose :: Either String ()
obligationManifestsClose = do
  qs <- qualifications
  mapM_ closed
    [steveDigestProviderQualification qs, steveBlobProviderQualification qs]
  where
    closed artifact = assert
      (Map.keysSet (qualificationEvidenceObligationDispositions
        (steveProviderIdentityEvidence artifact)) == steveProviderRequiredObligationKeys artifact)
      ("obligation domain is not closed for " <> show (steveProviderLabel artifact))

assumptionsRemainExplicit :: Either String ()
assumptionsRemainExplicit = do
  blob <- blobArtifact
  let conditions = qualificationClaimConditions (steveProviderIdentityClaim blob)
      evidenceAssumptions = qualificationEvidenceAssumptionRefs
        (steveProviderIdentityEvidence blob)
      admissionConditions = Map.keysSet $ qualificationAdmissionConditionDispositions
        (steveProviderIdentityAdmission blob)
  assert (conditions == evidenceAssumptions) "evidence lost or invented assumptions"
  assert (conditions == admissionConditions) "admission did not disposition every condition"

firstCompetence :: SteveProviderQualificationArtifact -> Either String CheckedProviderEvidenceProducerCompetence
firstCompetence artifact = case steveProviderEvidenceCompetences artifact of
  first : _ -> Right first
  [] -> Left "provider has no evidence competence"

lookupOperation :: Text -> SteveProviderQualificationArtifact -> Either String ProviderOperationContract
lookupOperation key artifact = maybe
  (Left ("missing provider operation: " <> show key))
  Right
  (Map.lookup (ProviderOperationKey key)
    (providerContractOperations (steveProviderContract artifact)))

onlyResidue :: ProviderOperationContract -> Either String ProviderResourceResidue
onlyResidue operation = case Map.elems (providerOperationOutcomeResidues operation) of
  [residue] -> Right residue
  residues -> Left ("expected one residue, got " <> show (length residues))

assertBorrowedNotConsumed :: ProviderResourceKey -> ProviderResourceResidue -> Either String ()
assertBorrowedNotConsumed key residue = do
  assert (Set.member key (providerResidueBorrowedInputs residue)) "input is not borrowed"
  assert (not (Set.member key (providerResidueConsumedInputs residue))) "borrowed input was consumed"

assertAdmitted :: SteveProviderQualificationArtifact -> Either String ()
assertAdmitted artifact = case checkedQualificationAdmissionDecision
    (steveProviderCheckedAdmission artifact) of
  QualificationAdmitted -> Right ()
  QualificationRejected reasons -> Left ("qualification rejected: " <> show reasons)

qualifications :: Either String SteveProviderQualifications
qualifications = mapLeft show materializeSteveProviderQualifications

digestArtifact :: Either String SteveProviderQualificationArtifact
digestArtifact = steveDigestProviderQualification <$> qualifications

blobArtifact :: Either String SteveProviderQualificationArtifact
blobArtifact = steveBlobProviderQualification <$> qualifications

emptyResidue :: ProviderResourceResidue
emptyResidue = ProviderResourceResidue Set.empty Set.empty Set.empty Set.empty Set.empty

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
