{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.ProviderReplacementQualification
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InstanceRevision (..)
  , InterfaceRevision (..)
  , RealizationRevision (..)
  )
import Phil.Examples.Steve.ProviderQualifications
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "qualified BlobProvider replacement is admitted at the Steve application boundary"
        qualifiedReplacementAccepts
    , test "replacement preserves Steve provider occurrence and architecture instance"
        abstractBindingPreserved
    , test "rejected replacement admission fails closed"
        rejectedReplacementFailsClosed
    , test "provider-occurrence substitution fails closed"
        occurrenceMismatchFailsClosed
    , test "public-interface substitution fails closed"
        interfaceMismatchFailsClosed
    , test "predecessor evidence cannot be inherited by a replacement"
        inheritedEvidenceFailsClosed
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: INT-006 " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: INT-006 " <> label <> " -- " <> detail) >> pure False

qualifiedReplacementAccepts :: Either String ()
qualifiedReplacementAccepts = do
  (artifact, prior, replacement) <- substitutionFixture
  checked <- mapLeft show $ checkProviderReplacementQualification
    prior replacement (reusePlan prior replacement artifact)
  assert
    (checkedProviderReplacementRequiredInterface checked
      == qualificationClaimRequiredInterface (steveProviderIdentityClaim artifact))
    "replacement changed the public BlobProvider interface"
  assert
    (checkedProviderReplacementOccurrence checked
      == qualificationAdmissionProviderOccurrence (steveProviderIdentityAdmission artifact))
    "replacement changed the Steve BlobProvider occurrence"

abstractBindingPreserved :: Either String ()
abstractBindingPreserved = do
  (artifact, prior, replacement) <- substitutionFixture
  checked <- mapLeft show $ checkProviderReplacementQualification
    prior replacement (reusePlan prior replacement artifact)
  assert
    (checkedProviderReplacementInstanceRevision checked == steveApplicationInstance)
    "provider replacement changed the Steve ArchitectureInstance"
  assert
    (checkedProviderReplacementPriorSubject checked
      == qualificationClaimSubject (steveProviderIdentityClaim artifact))
    "prior subject lost the materialized PROV-016 identity"
  assert
    (checkedProviderReplacementPriorSubject checked
      /= checkedProviderReplacementNewSubject checked)
    "replacement did not select an independent implementation subject"
  assert
    (checkedProviderReplacementPriorRealizationRevision checked
      /= checkedProviderReplacementNewRealizationRevision checked)
    "replacement did not change ArchitectureRealization identity"

rejectedReplacementFailsClosed :: Either String ()
rejectedReplacementFailsClosed = do
  (artifact, prior, replacement) <- substitutionFixture
  let admission = (providerReplacementAdmission replacement)
        { qualificationAdmissionDecision =
            QualificationRejected (Set.singleton "replacement-not-qualified")
        }
      rejected = replacement { providerReplacementAdmission = admission }
  case checkProviderReplacementQualification
      prior rejected (reusePlan prior rejected artifact) of
    Left (ProviderReplacementNewAdmissionRejected reasons) ->
      assert (reasons == Set.singleton "replacement-not-qualified")
        "wrong fail-closed rejection reason"
    other -> Left ("rejected replacement was not rejected: " <> show other)

occurrenceMismatchFailsClosed :: Either String ()
occurrenceMismatchFailsClosed = do
  (artifact, prior, replacement) <- substitutionFixture
  let admission = (providerReplacementAdmission replacement)
        { qualificationAdmissionProviderOccurrence = "steve.blob-provider.wrong-occurrence" }
      mismatched = replacement { providerReplacementAdmission = admission }
      expected = qualificationAdmissionProviderOccurrence
        (steveProviderIdentityAdmission artifact)
  case checkProviderReplacementQualification
      prior mismatched (reusePlan prior mismatched artifact) of
    Left (ProviderReplacementOccurrenceMismatch actualExpected actual) -> do
      assert (actualExpected == expected) "wrong expected provider occurrence"
      assert (actual == "steve.blob-provider.wrong-occurrence")
        "wrong mismatched provider occurrence"
    other -> Left ("occurrence-changing replacement was accepted: " <> show other)

interfaceMismatchFailsClosed :: Either String ()
interfaceMismatchFailsClosed = do
  (artifact, prior, _) <- substitutionFixture
  let wrongInterface = InterfaceRevision "steve.blob-provider.incompatible:v1"
      baseClaim = steveProviderIdentityClaim artifact
      claim = baseClaim
        { qualificationClaimRequiredInterface = wrongInterface
        , qualificationClaimSubject = replacementSubject
        }
      replacement = replacementSide artifact claim
  case checkProviderReplacementQualification
      prior replacement (reusePlan prior replacement artifact) of
    Left (ProviderReplacementInterfaceMismatch expected actual) -> do
      assert
        (expected == qualificationClaimRequiredInterface baseClaim)
        "wrong expected BlobProvider interface"
      assert (actual == wrongInterface) "wrong incompatible BlobProvider interface"
    other -> Left ("interface-changing replacement was accepted: " <> show other)

inheritedEvidenceFailsClosed :: Either String ()
inheritedEvidenceFailsClosed = do
  (artifact, prior, replacement) <- substitutionFixture
  let inherited = replacement
        { providerReplacementEvidence = providerReplacementEvidence prior }
  case checkProviderReplacementQualification
      prior inherited (reusePlan prior inherited artifact) of
    Left (ProviderReplacementNewIdentityError _) -> Right ()
    other -> Left ("predecessor evidence qualified replacement: " <> show other)

substitutionFixture
  :: Either String
       ( SteveProviderQualificationArtifact
       , ProviderReplacementSide
       , ProviderReplacementSide
       )
substitutionFixture = do
  qualifications <- mapLeft show materializeSteveProviderQualifications
  let artifact = steveBlobProviderQualification qualifications
      prior = ProviderReplacementSide
        { providerReplacementClaim = steveProviderIdentityClaim artifact
        , providerReplacementEvidence = steveProviderIdentityEvidence artifact
        , providerReplacementAdmission = steveProviderIdentityAdmission artifact
        , providerReplacementInstanceRevision = steveApplicationInstance
        , providerReplacementRealizationRevision = stevePriorRealization
        }
      claim = (steveProviderIdentityClaim artifact)
        { qualificationClaimSubject = replacementSubject }
      replacement = replacementSide artifact claim
  pure (artifact, prior, replacement)

replacementSide
  :: SteveProviderQualificationArtifact
  -> ProviderQualificationClaimIdentityInput
  -> ProviderReplacementSide
replacementSide artifact claim = ProviderReplacementSide
  { providerReplacementClaim = claim
  , providerReplacementEvidence = evidence
  , providerReplacementAdmission = admission
  , providerReplacementInstanceRevision = steveApplicationInstance
  , providerReplacementRealizationRevision = steveReplacementRealization
  }
  where
    baseEvidence = steveProviderIdentityEvidence artifact
    evidence = baseEvidence
      { qualificationEvidenceClaimRevision = deriveQualificationClaimRevision claim
      , qualificationEvidenceRefs = freshenSet
          (qualificationEvidenceRefs baseEvidence)
      , qualificationEvidenceProofRefs = freshenSet
          (qualificationEvidenceProofRefs baseEvidence)
      , qualificationEvidenceTranslationValidationRefs = freshenSet
          (qualificationEvidenceTranslationValidationRefs baseEvidence)
      , qualificationEvidenceRuntimeEnforcementRefs = freshenSet
          (qualificationEvidenceRuntimeEnforcementRefs baseEvidence)
      , qualificationEvidenceValidityDependencies = freshenSet
          (qualificationEvidenceValidityDependencies baseEvidence)
      }
    baseAdmission = steveProviderIdentityAdmission artifact
    admission = baseAdmission
      { qualificationAdmissionClaimRevision = deriveQualificationClaimRevision claim
      , qualificationAdmissionEvidenceRevision = deriveQualificationEvidenceRevision evidence
      , qualificationAdmissionRequiredInterface = qualificationClaimRequiredInterface claim
      , qualificationAdmissionRealizationContextRevision =
          qualificationAdmissionRealizationContextRevision baseAdmission
            <> ":replacement:v1"
      , qualificationAdmissionSelectedArtifactRuntimeAbi =
          fmap (<> ":replacement:v1")
            (qualificationAdmissionSelectedArtifactRuntimeAbi baseAdmission)
      , qualificationAdmissionDecision = QualificationAdmitted
      }

reusePlan
  :: ProviderReplacementSide
  -> ProviderReplacementSide
  -> SteveProviderQualificationArtifact
  -> Map.Map ProviderReplacementEvidenceReference ProviderReplacementEvidenceReuse
reusePlan prior replacement artifact = Map.fromList
  [ let ref = ProviderReplacementEvidenceReference AssumptionReference assumption
    in (ref, ProviderReplacementEvidenceReuse
      { providerReplacementReuseReference = ref
      , providerReplacementReusePriorClaimRevision =
          deriveQualificationClaimRevision (providerReplacementClaim prior)
      , providerReplacementReuseNewClaimRevision =
          deriveQualificationClaimRevision (providerReplacementClaim replacement)
      , providerReplacementReuseValidityScopeRevision =
          "steve.int006.shared-assumption:v1:" <> assumption
      })
  | assumption <- Set.toAscList
      (qualificationEvidenceAssumptionRefs (steveProviderIdentityEvidence artifact))
  ]

freshenSet :: Set.Set Text -> Set.Set Text
freshenSet = Set.map (<> ":replacement:v1")

replacementSubject :: ProviderQualificationSubject
replacementSubject = SemanticProviderImplementation
  (DefinitionRevision "steve.blob-provider.replacement:v1")

steveApplicationInstance :: InstanceRevision
steveApplicationInstance = InstanceRevision "steve.application.instance:v1"

stevePriorRealization, steveReplacementRealization :: RealizationRevision
stevePriorRealization = RealizationRevision "steve.application.realization:prov016:v1"
steveReplacementRealization =
  RealizationRevision "steve.application.realization:replacement:v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
