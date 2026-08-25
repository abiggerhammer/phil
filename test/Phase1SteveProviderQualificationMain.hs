{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Authority (AuthorityOperationKey (..), AuthoritySubjectKey (..))
import Phil.Core.AuthorityConfinement (AuthorityUse (..))
import Phil.Core.ProviderAuthorityQualification
import Phil.Core.ProviderEvidenceQualification
import Phil.Core.ProviderLawQualification
import Phil.Core.ProviderLifecycleQualification
import Phil.Core.ProviderQualification
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.Static (SemanticForm (..))
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
  assert (steveProviderLabel digest == "DigestProvider[SHA256]") "wrong digest artifact label"
  assert (steveProviderLabel blob == "BlobProvider") "wrong blob artifact label"
  assertAdmitted digest
  assertAdmitted blob

digestPropositionIsExact :: Either String ()
digestPropositionIsExact = do
  digest <- digestArtifact
  competence <- case steveProviderEvidenceCompetences digest of
    first : _ -> Right first
    [] -> Left "DigestProvider has no evidence competence"
  let expected = Atom "DigestMatches"
        [ RefOpaque (SortStableId "content-id:sha256") "role:computed-content-id"
        , RefOpaque
            (SortStableId "provider-evidence-subject")
            "role:steve-put-candidate-object"
        ]
  assert (checkedProviderEvidenceProposition competence == expected)
    "DigestMatches did not preserve id parameter + stable object subject"

digestBorrowIsObservationOnly :: Either String ()
digestBorrowIsObservationOnly = do
  digest <- digestArtifact
  competence <- case steveProviderEvidenceCompetences digest of
    first : _ -> Right first
    [] -> Left "DigestProvider has no evidence competence"
  case checkedProviderEvidenceObservation competence of
    ScopedBorrowEvidenceObservation _ _ -> pure ()
    other -> Left ("digest evidence did not come from scoped borrow: " <> show other)
  assert
    (checkedProviderEvidenceSubject competence ==
      ProviderEvidenceSubjectKey "role:steve-put-candidate-object")
    "temporary borrow identity became evidence subject"

digestBorrowResidueIsNonconsuming :: Either String ()
digestBorrowResidueIsNonconsuming = do
  digest <- digestArtifact
  operation <- lookupOperation "digest.compute" digest
  residue <- onlyResidue operation
  let candidate = ProviderResourceKey "candidate-byte-view"
  assert (Set.member candidate (providerResidueBorrowedInputs residue))
    "digest compute did not retain candidate as borrowed input"
  assert (not (Set.member candidate (providerResidueConsumedInputs residue)))
    "digest compute consumed Steve's candidate owner"

blobInstallBorrowIsNonconsuming :: Either String ()
blobInstallBorrowIsNonconsuming = do
  blob <- blobArtifact
  operation <- lookupOperation "blob.install-if-absent" blob
  let candidate = ProviderResourceKey "steve-candidate-owner-borrow"
      residues = Map.elems (providerOperationOutcomeResidues operation)
  assert (length residues == 3) "installIfAbsent did not expose all three public outcomes"
  mapM_ (assertBorrowedNotConsumed candidate) residues
  where
    assertBorrowedNotConsumed candidate residue = do
      assert (Set.member candidate (providerResidueBorrowedInputs residue))
        "install outcome failed to preserve candidate borrow"
      assert (not (Set.member candidate (providerResidueConsumedInputs residue)))
        "install outcome consumed Steve's candidate owner"

blobWholeProviderLayersPresent :: Either String ()
blobWholeProviderLayersPresent = do
  blob <- blobArtifact
  assert (steveProviderCheckedState blob /= Nothing) "BlobProvider lacks state qualification"
  assert (not (null (steveProviderLaws blob))) "BlobProvider lacks no-replace law"
  assert (steveProviderCheckedLifecycle blob /= Nothing) "BlobProvider lacks lifecycle qualification"
  let checkedAuthority = steveProviderCheckedAuthority blob
  assert (not (Set.null (checkedProviderAuthorityExtra checkedAuthority)))
    "BlobProvider fixture failed to exercise rich-internal authority"

blobNoReplaceRejectsReplacement :: Either String ()
blobNoReplaceRejectsReplacement = do
  blob <- blobArtifact
  law <- case steveProviderLaws blob of
    (raw, _) : _ -> Right raw
    [] -> Left "BlobProvider has no law artifact"
  let installed = ProviderImplementationEvent
        (ProviderOperationKey "blob.install-if-absent")
        (ProviderOutcomeKey "impl.blob.install.installed")
  case checkProviderLawTrace
      (steveProviderCheckedSemantic blob)
      law
      [installed, installed] of
    Left (ProviderLawViolation _ 1 _ _) -> Right ()
    other -> Left ("second installed event did not violate no-replace: " <> show other)

blobPartialPublicationRejected :: Either String ()
blobPartialPublicationRejected = do
  blob <- blobArtifact
  contract <- maybe (Left "BlobProvider lacks lifecycle contract") Right
    (steveProviderLifecycleContract blob)
  model <- maybe (Left "BlobProvider lacks lifecycle model") Right
    (steveProviderLifecycleModel blob)
  let point = ProviderLifecyclePoint
        (ProviderOperationKey "blob.install-if-absent")
        (ProviderInterruptionPointKey "install.after-publication-before-return")
      partial = ProviderInterruptionObservation
        { providerInterruptionObservationBoundary =
            ProviderObservationBoundaryKey "steve.blob.client-visible-namespace.v1"
        , providerInterruptionObservableState =
            ProviderObservableStateKey "object.partially-committed"
        , providerInterruptionCleanupResidue = emptyResidue
        , providerInterruptionRetryDisposition = ProviderRetrySameOperation
        }
      broken = ProviderLifecycleModel
        (Map.insert point (Set.singleton partial)
          (providerLifecycleImplementationObservations model))
  case checkProviderLifecycleQualification
      (steveProviderCheckedSemantic blob) contract broken of
    Left (ProviderLifecycleForbiddenObservableState actualPoint actualState) -> do
      assert (actualPoint == point) "wrong interruption point rejected"
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
      dispositions = checkedProviderAuthorityDispositions checked
      expectedAssumption = ProviderAuthorityAssumptionKey
        "assumption:steve.blob.backing-authority-confined.v1"
  assert (checkedProviderAuthorityExtra checked == Set.fromList [overwrite, deleteUse])
    "BlobProvider extra authority set is not exact"
  assert
    (Map.lookup overwrite dispositions ==
      Just (ExtraAuthorityAssumptionDependent expectedAssumption))
    "overwrite authority lacks explicit confinement disposition"
  assert
    (Map.lookup deleteUse dispositions ==
      Just (ExtraAuthorityAssumptionDependent expectedAssumption))
    "delete authority lacks explicit confinement disposition"

obligationManifestsClose :: Either String ()
obligationManifestsClose = do
  qs <- qualifications
  mapM_ checkArtifact
    [steveDigestProviderQualification qs, steveBlobProviderQualification qs]
  where
    checkArtifact artifact =
      assert
        (Map.keysSet
          (qualificationEvidenceObligationDispositions
            (steveProviderIdentityEvidence artifact))
          == steveProviderRequiredObligationKeys artifact)
        ("obligation disposition domain does not close for " <>
          show (steveProviderLabel artifact))

assumptionsRemainExplicit :: Either String ()
assumptionsRemainExplicit = do
  blob <- blobArtifact
  let claimConditions = qualificationClaimConditions (steveProviderIdentityClaim blob)
      evidenceAssumptions = qualificationEvidenceAssumptionRefs
        (steveProviderIdentityEvidence blob)
      admissionConditions = Map.keysSet
        (qualificationAdmissionConditionDispositions
          (steveProviderIdentityAdmission blob))
  assert (claimConditions == evidenceAssumptions)
    "BlobProvider evidence lost or invented conditional assumptions"
  assert (claimConditions == admissionConditions)
    "BlobProvider admission did not disposition every claim condition"

lookupOperation :: Text -> SteveProviderQualificationArtifact -> Either String ProviderOperationContract
lookupOperation key artifact =
  maybe (Left ("missing provider operation: " <> show key)) Right $
    Map.lookup (ProviderOperationKey key)
      (providerContractOperations (steveProviderContract artifact))

onlyResidue :: ProviderOperationContract -> Either String ProviderResourceResidue
onlyResidue operation = case Map.elems (providerOperationOutcomeResidues operation) of
  [residue] -> Right residue
  residues -> Left ("expected one outcome residue, got " <> show (length residues))

assertAdmitted :: SteveProviderQualificationArtifact -> Either String ()
assertAdmitted artifact = case checkedQualificationAdmissionDecision
    (steveProviderCheckedAdmission artifact) of
  QualificationAdmitted -> Right ()
  QualificationRejected reasons ->
    Left ("provider pressure qualification was rejected: " <> show reasons)

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
