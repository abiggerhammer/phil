{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.DeploymentAuthority
import Phil.Assurance.DeploymentAuthorityCertification
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
    [ test "certified authority issuance and use accept exact current qualification" validCertifiedIssueAndUse
    , test "valid authority policy and grant reflect all kernel facts" validFactsAreAllTrue
    , test "policy semantic disagreement fails closed" policyDisagreementRejects
    , test "grant semantic disagreement fails closed" grantDisagreementRejects
    , test "issuance rejects invalid qualification predecessor" issuedQualificationDisagreementRejects
    , test "use rejects non-current grant fact" usableCurrentDisagreementRejects
    , test "native authority diagnostics retain precedence" nativeDiagnosticPrecedence
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validCertifiedIssueAndUse :: Either String ()
validCertifiedIssueAndUse = do
  grant <- mapLeft show $ issueDeploymentAuthorityCertified
    currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification) authorityPolicy
  mapLeft show $ checkDeploymentAuthorityGrantCertified
    160 deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification) authorityPolicy grant

validFactsAreAllTrue :: Either String ()
validFactsAreAllTrue = do
  grant <- mapLeft show $ issueDeploymentAuthority
    currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification) authorityPolicy
  let policyFacts = deploymentAuthorityPolicyKernelFacts
        deploymentPlan deploymentQualification authorityPolicy
      grantFacts = deploymentAuthorityGrantKernelFacts
        deploymentQualification authorityPolicy grant
  assert
    ( and
        [ authorityKernelPolicyWellFormed policyFacts
        , authorityKernelDeploymentPolicyExact policyFacts
        , authorityKernelClaimPlanned policyFacts
        , authorityKernelClaimQualified policyFacts
        , authorityKernelGrantPolicyExact grantFacts
        , authorityKernelGrantQualificationExact grantFacts
        , authorityKernelGrantClaimExact grantFacts
        , authorityKernelGrantActionExact grantFacts
        , authorityKernelGrantResourceExact grantFacts
        , authorityKernelGrantValidityEndExact grantFacts
        , authorityKernelGrantContentIdentityValid grantFacts
        ]
    )
    ("valid authority reflected a false fact: " <> show (policyFacts, grantFacts))

policyDisagreementRejects :: Either String ()
policyDisagreementRejects =
  let facts = (deploymentAuthorityPolicyKernelFacts
        deploymentPlan deploymentQualification authorityPolicy)
        { authorityKernelDeploymentPolicyExact = False }
  in case verifyDeploymentAuthorityPolicyKernelFacts facts of
    Left (DeploymentAuthorityCertificationPolicyKernelDisagreement rejected) ->
      assert (rejected == facts) "policy disagreement lost exact reflected facts"
    other -> Left ("policy disagreement did not fail closed: " <> show other)

grantDisagreementRejects :: Either String ()
grantDisagreementRejects = do
  grant <- mapLeft show $ issueDeploymentAuthority
    currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification) authorityPolicy
  let facts = (deploymentAuthorityGrantKernelFacts
        deploymentQualification authorityPolicy grant)
        { authorityKernelGrantResourceExact = False }
  case verifyDeploymentAuthorityGrantKernelFacts facts of
    Left (DeploymentAuthorityCertificationGrantKernelDisagreement rejected) ->
      assert (rejected == facts) "grant disagreement lost exact reflected facts"
    other -> Left ("grant disagreement did not fail closed: " <> show other)

issuedQualificationDisagreementRejects :: Either String ()
issuedQualificationDisagreementRejects =
  case verifyDeploymentAuthorityIssuedKernelFacts False True True True of
    Left (DeploymentAuthorityCertificationIssuedKernelDisagreement False True True True) -> Right ()
    other -> Left ("invalid qualification predecessor passed issuance gate: " <> show other)

usableCurrentDisagreementRejects :: Either String ()
usableCurrentDisagreementRejects =
  case verifyDeploymentAuthorityUsableKernelFacts True True True False of
    Left (DeploymentAuthorityCertificationUsableKernelDisagreement True True True False) -> Right ()
    other -> Left ("non-current grant passed use-time gate: " <> show other)

nativeDiagnosticPrecedence :: Either String ()
nativeDiagnosticPrecedence =
  let wrongPolicy = authorityPolicy
        { deploymentAuthorityRequiredDeploymentPolicy = otherDeploymentPolicy }
  in case issueDeploymentAuthorityCertified
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
      (Just deploymentQualification) wrongPolicy of
    Left (DeploymentAuthorityCertificationNativeError
      (DeploymentAuthorityDeploymentPolicyMismatch expected actual)) ->
        assert (expected == deploymentPolicy && actual == otherDeploymentPolicy)
          "certification wrapper changed native deployment-policy mismatch payload"
    other -> Left ("native diagnostic was not preserved ahead of kernel gates: " <> show other)

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

secretReleaseClaim :: RevisionId
secretReleaseClaim = RevisionId "claim.deployment.secret-release.v1"

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
