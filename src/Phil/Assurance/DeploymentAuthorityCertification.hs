module Phil.Assurance.DeploymentAuthorityCertification
  ( DeploymentAuthorityPolicyKernelFacts (..)
  , DeploymentAuthorityGrantKernelFacts (..)
  , DeploymentAuthorityCertificationError (..)
  , deploymentAuthorityPolicyKernelFacts
  , deploymentAuthorityGrantKernelFacts
  , verifyDeploymentAuthorityPolicyKernelFacts
  , verifyDeploymentAuthorityGrantKernelFacts
  , verifyDeploymentAuthorityIssuedKernelFacts
  , verifyDeploymentAuthorityUsableKernelFacts
  , issueDeploymentAuthorityCertified
  , checkDeploymentAuthorityGrantCertified
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.DeploymentAuthority
import Phil.Assurance.DeploymentQualification
import Phil.Assurance.DeploymentQualificationCertification
import qualified DeploymentAuthorityKernel as Kernel

-- | Native reflections of DeploymentAuthorityPolicyAdmissible.
data DeploymentAuthorityPolicyKernelFacts = DeploymentAuthorityPolicyKernelFacts
  { authorityKernelPolicyWellFormed :: Bool
  , authorityKernelDeploymentPolicyExact :: Bool
  , authorityKernelClaimPlanned :: Bool
  , authorityKernelClaimQualified :: Bool
  }
  deriving (Eq, Show)

-- | Native reflections of DeploymentAuthorityGrantMatches.
data DeploymentAuthorityGrantKernelFacts = DeploymentAuthorityGrantKernelFacts
  { authorityKernelGrantPolicyExact :: Bool
  , authorityKernelGrantQualificationExact :: Bool
  , authorityKernelGrantClaimExact :: Bool
  , authorityKernelGrantActionExact :: Bool
  , authorityKernelGrantResourceExact :: Bool
  , authorityKernelGrantValidityEndExact :: Bool
  , authorityKernelGrantContentIdentityValid :: Bool
  }
  deriving (Eq, Show)

data DeploymentAuthorityCertificationError
  = DeploymentAuthorityCertificationNativeError DeploymentAuthorityError
  | DeploymentAuthorityCertificationQualificationError
      DeploymentQualificationCertificationError
  | DeploymentAuthorityCertificationPolicyKernelDisagreement
      DeploymentAuthorityPolicyKernelFacts
  | DeploymentAuthorityCertificationGrantKernelDisagreement
      DeploymentAuthorityGrantKernelFacts
  | DeploymentAuthorityCertificationIssuedKernelDisagreement
      Bool Bool Bool Bool
  | DeploymentAuthorityCertificationUsableKernelDisagreement
      Bool Bool Bool Bool
  deriving (Eq, Show)

issueDeploymentAuthorityCertified
  :: Integer
  -> DeploymentPlan
  -> Map.Map DeploymentEvidenceKey DeploymentDomainEvidence
  -> Map.Map DeploymentCompositionEvidenceKey DeploymentCompositionEvidence
  -> Maybe DeploymentQualification
  -> DeploymentAuthorityPolicy
  -> Either DeploymentAuthorityCertificationError DeploymentAuthorityGrant
issueDeploymentAuthorityCertified
    current plan domainEvidence compositionEvidence maybeQualification policy = do
  grant <- mapLeft DeploymentAuthorityCertificationNativeError $
    issueDeploymentAuthority
      current plan domainEvidence compositionEvidence maybeQualification policy
  qualification <- requireQualification maybeQualification
  mapLeft DeploymentAuthorityCertificationQualificationError $
    verifyDeploymentQualificationCertification
      current plan domainEvidence compositionEvidence maybeQualification
  let policyFacts = deploymentAuthorityPolicyKernelFacts plan qualification policy
      grantFacts = deploymentAuthorityGrantKernelFacts qualification policy grant
  policyAccepted <- verifyDeploymentAuthorityPolicyKernelFacts policyFacts
  grantAccepted <- verifyDeploymentAuthorityGrantKernelFacts grantFacts
  verifyDeploymentAuthorityIssuedKernelFacts
    True
    policyAccepted
    grantAccepted
    (deploymentAuthorityGrantValidFrom grant == current)
  pure grant

checkDeploymentAuthorityGrantCertified
  :: Integer
  -> DeploymentPlan
  -> Map.Map DeploymentEvidenceKey DeploymentDomainEvidence
  -> Map.Map DeploymentCompositionEvidenceKey DeploymentCompositionEvidence
  -> Maybe DeploymentQualification
  -> DeploymentAuthorityPolicy
  -> DeploymentAuthorityGrant
  -> Either DeploymentAuthorityCertificationError ()
checkDeploymentAuthorityGrantCertified
    current plan domainEvidence compositionEvidence maybeQualification policy grant = do
  mapLeft DeploymentAuthorityCertificationNativeError $
    checkDeploymentAuthorityGrant
      current plan domainEvidence compositionEvidence maybeQualification policy grant
  qualification <- requireQualification maybeQualification
  mapLeft DeploymentAuthorityCertificationQualificationError $
    verifyDeploymentQualificationCertification
      current plan domainEvidence compositionEvidence maybeQualification
  let policyFacts = deploymentAuthorityPolicyKernelFacts plan qualification policy
      grantFacts = deploymentAuthorityGrantKernelFacts qualification policy grant
  policyAccepted <- verifyDeploymentAuthorityPolicyKernelFacts policyFacts
  grantAccepted <- verifyDeploymentAuthorityGrantKernelFacts grantFacts
  verifyDeploymentAuthorityUsableKernelFacts
    True
    policyAccepted
    grantAccepted
    ( pointWithin current
        (deploymentAuthorityGrantValidFrom grant)
        (deploymentAuthorityGrantValidUntil grant)
    )

deploymentAuthorityPolicyKernelFacts
  :: DeploymentPlan
  -> DeploymentQualification
  -> DeploymentAuthorityPolicy
  -> DeploymentAuthorityPolicyKernelFacts
deploymentAuthorityPolicyKernelFacts plan qualification policy =
  DeploymentAuthorityPolicyKernelFacts
    { authorityKernelPolicyWellFormed =
        not (Text.null
          (unDeploymentAuthorityPolicyRevision
            (deploymentAuthorityPolicyRevision policy)))
          && not (Text.null (deploymentAuthorityAction policy))
          && not (Text.null (deploymentAuthorityResource policy))
    , authorityKernelDeploymentPolicyExact =
        deploymentAuthorityRequiredDeploymentPolicy policy == deploymentPlanPolicy plan
    , authorityKernelClaimPlanned =
        Map.member
          (deploymentAuthorityRequiredClaim policy)
          (deploymentPlanClaimDomains plan)
    , authorityKernelClaimQualified =
        Set.member
          (deploymentAuthorityRequiredClaim policy)
          (deploymentQualificationCoveredClaims qualification)
    }

deploymentAuthorityGrantKernelFacts
  :: DeploymentQualification
  -> DeploymentAuthorityPolicy
  -> DeploymentAuthorityGrant
  -> DeploymentAuthorityGrantKernelFacts
deploymentAuthorityGrantKernelFacts qualification policy grant =
  DeploymentAuthorityGrantKernelFacts
    { authorityKernelGrantPolicyExact =
        deploymentAuthorityGrantPolicyRevision grant
          == deploymentAuthorityPolicyRevision policy
    , authorityKernelGrantQualificationExact =
        deploymentAuthorityGrantQualificationId grant
          == deploymentQualificationId qualification
    , authorityKernelGrantClaimExact =
        deploymentAuthorityGrantClaim grant
          == deploymentAuthorityRequiredClaim policy
    , authorityKernelGrantActionExact =
        deploymentAuthorityGrantAction grant == deploymentAuthorityAction policy
    , authorityKernelGrantResourceExact =
        deploymentAuthorityGrantResource grant == deploymentAuthorityResource policy
    , authorityKernelGrantValidityEndExact =
        deploymentAuthorityGrantValidUntil grant
          == deploymentQualificationValidUntil qualification
    , authorityKernelGrantContentIdentityValid =
        deploymentAuthorityGrantId grant == deriveDeploymentAuthorityGrantId grant
    }

verifyDeploymentAuthorityPolicyKernelFacts
  :: DeploymentAuthorityPolicyKernelFacts
  -> Either DeploymentAuthorityCertificationError Bool
verifyDeploymentAuthorityPolicyKernelFacts facts =
  if accepted
    then Right True
    else Left (DeploymentAuthorityCertificationPolicyKernelDisagreement facts)
  where
    accepted = Kernel.decideDeploymentAuthorityPolicyAdmissibleByFacts
      (authorityKernelPolicyWellFormed facts)
      (authorityKernelDeploymentPolicyExact facts)
      (authorityKernelClaimPlanned facts)
      (authorityKernelClaimQualified facts)

verifyDeploymentAuthorityGrantKernelFacts
  :: DeploymentAuthorityGrantKernelFacts
  -> Either DeploymentAuthorityCertificationError Bool
verifyDeploymentAuthorityGrantKernelFacts facts =
  if accepted
    then Right True
    else Left (DeploymentAuthorityCertificationGrantKernelDisagreement facts)
  where
    accepted = Kernel.decideDeploymentAuthorityGrantMatchesByFacts
      (authorityKernelGrantPolicyExact facts)
      (authorityKernelGrantQualificationExact facts)
      (authorityKernelGrantClaimExact facts)
      (authorityKernelGrantActionExact facts)
      (authorityKernelGrantResourceExact facts)
      (authorityKernelGrantValidityEndExact facts)
      (authorityKernelGrantContentIdentityValid facts)

verifyDeploymentAuthorityIssuedKernelFacts
  :: Bool
  -> Bool
  -> Bool
  -> Bool
  -> Either DeploymentAuthorityCertificationError ()
verifyDeploymentAuthorityIssuedKernelFacts
    qualificationValid policyAdmissible grantMatches grantBeginsAtObservation =
  if Kernel.decideDeploymentAuthorityIssuedByFacts
      qualificationValid policyAdmissible grantMatches grantBeginsAtObservation
    then Right ()
    else Left (DeploymentAuthorityCertificationIssuedKernelDisagreement
      qualificationValid policyAdmissible grantMatches grantBeginsAtObservation)

verifyDeploymentAuthorityUsableKernelFacts
  :: Bool
  -> Bool
  -> Bool
  -> Bool
  -> Either DeploymentAuthorityCertificationError ()
verifyDeploymentAuthorityUsableKernelFacts
    qualificationValid policyAdmissible grantMatches grantCurrent =
  if Kernel.decideDeploymentAuthorityUsableByFacts
      qualificationValid policyAdmissible grantMatches grantCurrent
    then Right ()
    else Left (DeploymentAuthorityCertificationUsableKernelDisagreement
      qualificationValid policyAdmissible grantMatches grantCurrent)

requireQualification
  :: Maybe DeploymentQualification
  -> Either DeploymentAuthorityCertificationError DeploymentQualification
requireQualification maybeQualification = case maybeQualification of
  Nothing -> Left (DeploymentAuthorityCertificationNativeError
    (DeploymentAuthorityQualificationError DeploymentQualificationMissing))
  Just qualification -> Right qualification

pointWithin :: Integer -> Integer -> Integer -> Bool
pointWithin current validFrom validUntil =
  validFrom <= current && current <= validUntil

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
