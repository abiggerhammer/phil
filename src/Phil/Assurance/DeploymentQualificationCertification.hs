module Phil.Assurance.DeploymentQualificationCertification
  ( DeploymentQualificationKernelFacts (..)
  , DeploymentQualificationCertificationError (..)
  , deploymentQualificationKernelFacts
  , verifyDeploymentQualificationKernelFacts
  , verifyDeploymentQualificationCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Phil.Assurance.DeploymentQualification
import qualified DeploymentQualificationKernel as Kernel

-- | Exact native reflections of the thirteen facts proved equivalent to
-- DeploymentQualificationValid by PHIL-DEPLOY-QUAL-001.
data DeploymentQualificationKernelFacts = DeploymentQualificationKernelFacts
  { kernelTopologyIdentityValid :: Bool
  , kernelLinksWellFormed :: Bool
  , kernelClaimDomainsTotal :: Bool
  , kernelClaimDomainsSound :: Bool
  , kernelArtifactExact :: Bool
  , kernelPolicyExact :: Bool
  , kernelTopologyExact :: Bool
  , kernelClaimSetExact :: Bool
  , kernelIdentityValid :: Bool
  , kernelQualificationCurrent :: Bool
  , kernelEverySelectedDomainHasEvidence :: Bool
  , kernelNoExtraDomainBinding :: Bool
  , kernelCompositionEvidenceValid :: Bool
  }
  deriving (Eq, Show)

data DeploymentQualificationCertificationError
  = DeploymentQualificationCertificationNativeError DeploymentQualificationError
  | DeploymentQualificationCertificationKernelDisagreement
      DeploymentQualificationKernelFacts
  deriving (Eq, Show)

verifyDeploymentQualificationCertification
  :: Integer
  -> DeploymentPlan
  -> Map DeploymentEvidenceKey DeploymentDomainEvidence
  -> Map DeploymentCompositionEvidenceKey DeploymentCompositionEvidence
  -> Maybe DeploymentQualification
  -> Either DeploymentQualificationCertificationError ()
verifyDeploymentQualificationCertification
    current plan domainEvidenceRegistry compositionRegistry maybeQualification = do
  mapLeft DeploymentQualificationCertificationNativeError $
    checkDeploymentQualification
      current plan domainEvidenceRegistry compositionRegistry maybeQualification
  qualification <- case maybeQualification of
    Nothing -> Left (DeploymentQualificationCertificationNativeError
      DeploymentQualificationMissing)
    Just value -> Right value
  let facts = deploymentQualificationKernelFacts
        current plan domainEvidenceRegistry compositionRegistry qualification
  verifyDeploymentQualificationKernelFacts True facts

verifyDeploymentQualificationKernelFacts
  :: Bool
  -> DeploymentQualificationKernelFacts
  -> Either DeploymentQualificationCertificationError ()
verifyDeploymentQualificationKernelFacts qualificationPresent facts = do
  let qualificationAccepted = kernelAccepts facts
      availableAccepted = Kernel.decideDeploymentQualificationAvailableByFacts
        qualificationPresent qualificationAccepted
  unless (qualificationAccepted && availableAccepted) $
    Left (DeploymentQualificationCertificationKernelDisagreement facts)

deploymentQualificationKernelFacts
  :: Integer
  -> DeploymentPlan
  -> Map DeploymentEvidenceKey DeploymentDomainEvidence
  -> Map DeploymentCompositionEvidenceKey DeploymentCompositionEvidence
  -> DeploymentQualification
  -> DeploymentQualificationKernelFacts
deploymentQualificationKernelFacts
    current plan domainEvidenceRegistry compositionRegistry qualification =
  DeploymentQualificationKernelFacts
    { kernelTopologyIdentityValid =
        deploymentTopologyRevision topology == expectedTopologyIdentity
    , kernelLinksWellFormed = all linkWellFormed (Set.toAscList topologyLinks)
    , kernelClaimDomainsTotal = all claimHasSelectedDomain (Map.elems claimDomains)
    , kernelClaimDomainsSound = all (`Set.isSubsetOf` topologyDomains) (Map.elems claimDomains)
    , kernelArtifactExact =
        deploymentQualificationArtifact qualification == deploymentPlanArtifact plan
    , kernelPolicyExact =
        deploymentQualificationPolicy qualification == deploymentPlanPolicy plan
    , kernelTopologyExact =
        deploymentQualificationTopologyRevision qualification == deploymentTopologyRevision topology
    , kernelClaimSetExact =
        deploymentQualificationCoveredClaims qualification == Map.keysSet claimDomains
    , kernelIdentityValid =
        deploymentQualificationId qualification == deriveDeploymentQualificationId qualification
    , kernelQualificationCurrent = pointWithin
        current
        (deploymentQualificationValidFrom qualification)
        (deploymentQualificationValidUntil qualification)
    , kernelEverySelectedDomainHasEvidence =
        all selectedDomainHasEvidence (Set.toAscList topologyDomains)
    , kernelNoExtraDomainBinding =
        Map.keysSet (deploymentQualificationDomainEvidence qualification)
          `Set.isSubsetOf` topologyDomains
    , kernelCompositionEvidenceValid = compositionEvidenceValid
    }
  where
    topology = deploymentPlanTopology plan
    topologyLinks = deploymentTopologyLinks topology
    topologyDomains = Set.fromList (Map.elems (deploymentTopologyComponentDomains topology))
    claimDomains = deploymentPlanClaimDomains plan
    expectedTopologyIdentity = deriveDeploymentTopologyRevision
      (deploymentTopologyComponentDomains topology)
      topologyLinks

    linkWellFormed link =
      Set.member (deploymentLinkFrom link) topologyDomains
        && Set.member (deploymentLinkTo link) topologyDomains

    claimHasSelectedDomain domains =
      not (Set.null (Set.intersection domains topologyDomains))

    selectedDomainHasEvidence domain =
      case Map.lookup domain (deploymentQualificationDomainEvidence qualification) of
        Nothing -> False
        Just evidenceKey -> case Map.lookup evidenceKey domainEvidenceRegistry of
          Nothing -> False
          Just evidence ->
            deploymentDomainEvidenceDomain evidence == domain
              && deploymentDomainEvidenceArtifact evidence == deploymentPlanArtifact plan
              && deploymentDomainEvidencePolicy evidence == deploymentPlanPolicy plan
              && pointWithin
                current
                (deploymentDomainEvidenceValidFrom evidence)
                (deploymentDomainEvidenceValidUntil evidence)
              && intervalWithin
                (deploymentQualificationValidFrom qualification)
                (deploymentQualificationValidUntil qualification)
                (deploymentDomainEvidenceValidFrom evidence)
                (deploymentDomainEvidenceValidUntil evidence)
              && requiredClaims domain
                `Set.isSubsetOf` deploymentDomainEvidenceClaims evidence

    requiredClaims domain = Set.fromList
      [ claim
      | (claim, domains) <- Map.toAscList claimDomains
      , Set.member domain domains
      ]

    compositeTopology =
      Set.size topologyDomains > 1 || not (Set.null topologyLinks)

    compositionEvidenceValid
      | compositeTopology =
          case deploymentQualificationCompositionEvidence qualification of
            Nothing -> False
            Just evidenceKey -> case Map.lookup evidenceKey compositionRegistry of
              Nothing -> False
              Just evidence ->
                deploymentCompositionEvidenceArtifact evidence == deploymentPlanArtifact plan
                  && deploymentCompositionEvidencePolicy evidence == deploymentPlanPolicy plan
                  && deploymentCompositionEvidenceTopologyRevision evidence
                    == deploymentTopologyRevision topology
                  && pointWithin
                    current
                    (deploymentCompositionEvidenceValidFrom evidence)
                    (deploymentCompositionEvidenceValidUntil evidence)
                  && intervalWithin
                    (deploymentQualificationValidFrom qualification)
                    (deploymentQualificationValidUntil qualification)
                    (deploymentCompositionEvidenceValidFrom evidence)
                    (deploymentCompositionEvidenceValidUntil evidence)
                  && deploymentCompositionEvidenceDomains evidence == topologyDomains
                  && deploymentCompositionEvidenceLinks evidence == topologyLinks
                  && deploymentCompositionEvidenceClaims evidence == Map.keysSet claimDomains
      | otherwise = deploymentQualificationCompositionEvidence qualification == Nothing

kernelAccepts :: DeploymentQualificationKernelFacts -> Bool
kernelAccepts facts = Kernel.decideDeploymentQualificationByFacts
  (kernelTopologyIdentityValid facts)
  (kernelLinksWellFormed facts)
  (kernelClaimDomainsTotal facts)
  (kernelClaimDomainsSound facts)
  (kernelArtifactExact facts)
  (kernelPolicyExact facts)
  (kernelTopologyExact facts)
  (kernelClaimSetExact facts)
  (kernelIdentityValid facts)
  (kernelQualificationCurrent facts)
  (kernelEverySelectedDomainHasEvidence facts)
  (kernelNoExtraDomainBinding facts)
  (kernelCompositionEvidenceValid facts)

pointWithin :: Integer -> Integer -> Integer -> Bool
pointWithin current validFrom validUntil =
  validFrom <= current && current <= validUntil

intervalWithin :: Integer -> Integer -> Integer -> Integer -> Bool
intervalWithin innerFrom innerUntil outerFrom outerUntil =
  outerFrom <= innerFrom && innerUntil <= outerUntil

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
