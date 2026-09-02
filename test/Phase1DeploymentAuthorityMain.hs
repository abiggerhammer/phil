{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.DeploymentAuthority
import Phil.Assurance.DeploymentQualification
import Phil.Assurance.Types
  ( ArtifactIdentity (..)
  , ArtifactRef (..)
  , Digest (..)
  , RevisionId (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DEP-006 current valid qualification grants exact narrow authority" validQualificationGrants
    , test "DEP-006 missing qualification cannot produce authority" missingQualificationRejects
    , test "DEP-006 stale qualification cannot produce authority" staleQualificationRejects
    , test "DEP-006 authority policy must select exact deployment policy" wrongDeploymentPolicyRejects
    , test "DEP-006 authority policy cannot invent an unqualified claim" unplannedClaimRejects
    , test "DEP-006 grant remains bound to exact action/resource" tamperedGrantRejects
    , test "DEP-006 later stale qualification invalidates previously issued authority" staleGrantUseRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validQualificationGrants :: Either String ()
validQualificationGrants = do
  grant <- mapLeft show $ issueDeploymentAuthority
    currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification) authorityPolicy
  assert
    ( deploymentAuthorityGrantQualificationId grant == deploymentQualificationId deploymentQualification
      && deploymentAuthorityGrantClaim grant == secretReleaseClaim
      && deploymentAuthorityGrantAction grant == "secret.release"
      && deploymentAuthorityGrantResource grant == "secret://demo/api-key"
      && deploymentAuthorityGrantValidFrom grant == currentPoint
      && deploymentAuthorityGrantValidUntil grant == 180
    )
    "grant lost exact qualification/claim/action/resource/validity identity"
  mapLeft show $ checkDeploymentAuthorityGrant
    160 deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification) authorityPolicy grant

missingQualificationRejects :: Either String ()
missingQualificationRejects =
  case issueDeploymentAuthority
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
      Nothing authorityPolicy of
    Left (DeploymentAuthorityQualificationError DeploymentQualificationMissing) -> Right ()
    other -> Left ("authority was produced without qualification: " <> show other)

staleQualificationRejects :: Either String ()
staleQualificationRejects =
  case issueDeploymentAuthority
      181 deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
      (Just deploymentQualification) authorityPolicy of
    Left (DeploymentAuthorityQualificationError
      (DeploymentQualificationStale point validFrom validUntil)) ->
        assert (point == 181 && validFrom == 120 && validUntil == 180)
          "stale qualification rejection lost exact current validity interval"
    other -> Left ("stale qualification produced authority: " <> show other)

wrongDeploymentPolicyRejects :: Either String ()
wrongDeploymentPolicyRejects =
  let wrongPolicy = authorityPolicy
        { deploymentAuthorityRequiredDeploymentPolicy = otherDeploymentPolicy }
  in case issueDeploymentAuthority
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
      (Just deploymentQualification) wrongPolicy of
    Left (DeploymentAuthorityDeploymentPolicyMismatch expected actual) ->
      assert (expected == deploymentPolicy && actual == otherDeploymentPolicy)
        "authority policy mismatch lost exact deployment policy identity"
    other -> Left ("wrong deployment policy produced authority: " <> show other)

unplannedClaimRejects :: Either String ()
unplannedClaimRejects =
  let wrongPolicy = authorityPolicy
        { deploymentAuthorityRequiredClaim = unrelatedClaim }
  in case issueDeploymentAuthority
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
      (Just deploymentQualification) wrongPolicy of
    Left (DeploymentAuthorityClaimNotPlanned claim) ->
      assert (claim == unrelatedClaim)
        "unplanned claim rejection lost exact claim identity"
    other -> Left ("unplanned claim produced authority: " <> show other)

tamperedGrantRejects :: Either String ()
tamperedGrantRejects = do
  grant <- mapLeft show $ issueDeploymentAuthority
    currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification) authorityPolicy
  let tampered = grant { deploymentAuthorityGrantAction = "secret.rotate" }
  case checkDeploymentAuthorityGrant
      160 deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
      (Just deploymentQualification) authorityPolicy tampered of
    Left (DeploymentAuthorityGrantActionMismatch expected actual) ->
      assert (expected == "secret.release" && actual == "secret.rotate")
        "tampered grant rejection lost exact action identity"
    other -> Left ("tampered authority grant remained usable: " <> show other)

staleGrantUseRejects :: Either String ()
staleGrantUseRejects = do
  grant <- mapLeft show $ issueDeploymentAuthority
    currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification) authorityPolicy
  case checkDeploymentAuthorityGrant
      181 deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
      (Just deploymentQualification) authorityPolicy grant of
    Left (DeploymentAuthorityQualificationError
      (DeploymentQualificationStale point validFrom validUntil)) ->
        assert (point == 181 && validFrom == 120 && validUntil == 180)
          "stale grant-use rejection lost qualification validity identity"
    other -> Left ("authority survived stale qualification: " <> show other)

currentPoint :: Integer
currentPoint = 150

artifact :: ArtifactIdentity
artifact = ArtifactIdentity
  { artifactReference = ArtifactRef "artifact://phil/demo/qualified-service"
  , artifactDigest = Digest "sha256.qualified-service.v1"
  }

deploymentPolicy, otherDeploymentPolicy :: DeploymentPolicyRevision
deploymentPolicy = DeploymentPolicyRevision "deployment.policy.secret-release.v1"
otherDeploymentPolicy = DeploymentPolicyRevision "deployment.policy.unrelated.v1"

domain :: DeploymentDomainKey
domain = DeploymentDomainKey "domain.tee0"

secretReleaseClaim, unrelatedClaim :: RevisionId
secretReleaseClaim = RevisionId "claim.deployment.secret-release.v1"
unrelatedClaim = RevisionId "claim.deployment.unrelated.v1"

topology :: DeploymentTopology
topology = makeDeploymentTopology
  (Map.singleton "secret-service" domain)
  Set.empty

deploymentPlan :: DeploymentPlan
deploymentPlan = DeploymentPlan
  { deploymentPlanArtifact = artifact
  , deploymentPlanPolicy = deploymentPolicy
  , deploymentPlanTopology = topology
  , deploymentPlanClaimDomains = Map.singleton secretReleaseClaim (Set.singleton domain)
  }

domainEvidenceKey :: DeploymentEvidenceKey
domainEvidenceKey = DeploymentEvidenceKey "attestation.tee0.secret-release.v1"

domainEvidence :: DeploymentDomainEvidence
domainEvidence = DeploymentDomainEvidence
  { deploymentDomainEvidenceKey = domainEvidenceKey
  , deploymentDomainEvidenceArtifact = artifact
  , deploymentDomainEvidencePolicy = deploymentPolicy
  , deploymentDomainEvidenceDomain = domain
  , deploymentDomainEvidenceValidFrom = 100
  , deploymentDomainEvidenceValidUntil = 200
  , deploymentDomainEvidenceClaims = Set.singleton secretReleaseClaim
  }

domainEvidenceRegistry :: Map.Map DeploymentEvidenceKey DeploymentDomainEvidence
domainEvidenceRegistry = Map.singleton domainEvidenceKey domainEvidence

compositionEvidenceRegistry
  :: Map.Map DeploymentCompositionEvidenceKey DeploymentCompositionEvidence
compositionEvidenceRegistry = Map.empty

deploymentQualification :: DeploymentQualification
deploymentQualification = makeDeploymentQualification
  deploymentPlan
  (Map.singleton domain domainEvidenceKey)
  Nothing
  120
  180

authorityPolicy :: DeploymentAuthorityPolicy
authorityPolicy = DeploymentAuthorityPolicy
  { deploymentAuthorityPolicyRevision =
      DeploymentAuthorityPolicyRevision "authority.policy.secret-release.v1"
  , deploymentAuthorityRequiredDeploymentPolicy = deploymentPolicy
  , deploymentAuthorityRequiredClaim = secretReleaseClaim
  , deploymentAuthorityAction = "secret.release"
  , deploymentAuthorityResource = "secret://demo/api-key"
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
