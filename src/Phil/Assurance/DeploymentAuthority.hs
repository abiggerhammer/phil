{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.DeploymentAuthority
  ( DeploymentAuthorityPolicyRevision (..)
  , DeploymentAuthorityGrantId (..)
  , DeploymentAuthorityPolicy (..)
  , DeploymentAuthorityGrant (..)
  , DeploymentAuthorityError (..)
  , deriveDeploymentAuthorityGrantId
  , issueDeploymentAuthority
  , checkDeploymentAuthorityGrant
  ) where

import Control.Monad (unless, when)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.DeploymentQualification
import Phil.Assurance.Types
  ( Digest (..)
  , RevisionId (..)
  , digestText
  )

newtype DeploymentAuthorityPolicyRevision = DeploymentAuthorityPolicyRevision
  { unDeploymentAuthorityPolicyRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype DeploymentAuthorityGrantId = DeploymentAuthorityGrantId
  { unDeploymentAuthorityGrantId :: Text
  }
  deriving (Eq, Ord, Show)

-- | A narrow authority policy.  Qualification never yields ambient authority:
-- the caller must preselect one exact deployment policy, one exact covered
-- claim, and one exact action/resource pair.
data DeploymentAuthorityPolicy = DeploymentAuthorityPolicy
  { deploymentAuthorityPolicyRevision :: DeploymentAuthorityPolicyRevision
  , deploymentAuthorityRequiredDeploymentPolicy :: DeploymentPolicyRevision
  , deploymentAuthorityRequiredClaim :: RevisionId
  , deploymentAuthorityAction :: Text
  , deploymentAuthorityResource :: Text
  }
  deriving (Eq, Show)

-- | A qualification-gated authority grant.  It is evidence that one exact
-- action on one exact resource was admitted from one exact current
-- qualification.  It is not a generic capability and cannot outlive the
-- qualification that justified it.
data DeploymentAuthorityGrant = DeploymentAuthorityGrant
  { deploymentAuthorityGrantId :: DeploymentAuthorityGrantId
  , deploymentAuthorityGrantPolicyRevision :: DeploymentAuthorityPolicyRevision
  , deploymentAuthorityGrantQualificationId :: DeploymentQualificationId
  , deploymentAuthorityGrantClaim :: RevisionId
  , deploymentAuthorityGrantAction :: Text
  , deploymentAuthorityGrantResource :: Text
  , deploymentAuthorityGrantValidFrom :: Integer
  , deploymentAuthorityGrantValidUntil :: Integer
  }
  deriving (Eq, Show)

data DeploymentAuthorityError
  = DeploymentAuthorityQualificationError DeploymentQualificationError
  | DeploymentAuthorityPolicyRevisionEmpty
  | DeploymentAuthorityActionEmpty
  | DeploymentAuthorityResourceEmpty
  | DeploymentAuthorityDeploymentPolicyMismatch
      DeploymentPolicyRevision DeploymentPolicyRevision
  | DeploymentAuthorityClaimNotPlanned RevisionId
  | DeploymentAuthorityClaimNotQualified RevisionId
  | DeploymentAuthorityGrantPolicyMismatch
      DeploymentAuthorityPolicyRevision DeploymentAuthorityPolicyRevision
  | DeploymentAuthorityGrantQualificationMismatch
      DeploymentQualificationId DeploymentQualificationId
  | DeploymentAuthorityGrantClaimMismatch RevisionId RevisionId
  | DeploymentAuthorityGrantActionMismatch Text Text
  | DeploymentAuthorityGrantResourceMismatch Text Text
  | DeploymentAuthorityGrantNotYetValid Integer Integer
  | DeploymentAuthorityGrantExpired Integer Integer
  | DeploymentAuthorityGrantValidityMismatch Integer Integer
  | DeploymentAuthorityGrantIdentityMismatch
      DeploymentAuthorityGrantId DeploymentAuthorityGrantId
  deriving (Eq, Show)

deriveDeploymentAuthorityGrantId
  :: DeploymentAuthorityGrant
  -> DeploymentAuthorityGrantId
deriveDeploymentAuthorityGrantId grant = DeploymentAuthorityGrantId
  ("deployment.authority.sha256." <> unDigest (digestText payload))
  where
    payload = Text.intercalate "|"
      [ "policy=" <> unDeploymentAuthorityPolicyRevision
          (deploymentAuthorityGrantPolicyRevision grant)
      , "qualification=" <> unDeploymentQualificationId
          (deploymentAuthorityGrantQualificationId grant)
      , "claim=" <> unRevisionId (deploymentAuthorityGrantClaim grant)
      , "action=" <> deploymentAuthorityGrantAction grant
      , "resource=" <> deploymentAuthorityGrantResource grant
      , "valid_from=" <> Text.pack (show (deploymentAuthorityGrantValidFrom grant))
      , "valid_until=" <> Text.pack (show (deploymentAuthorityGrantValidUntil grant))
      ]

issueDeploymentAuthority
  :: Integer
  -> DeploymentPlan
  -> Map.Map DeploymentEvidenceKey DeploymentDomainEvidence
  -> Map.Map DeploymentCompositionEvidenceKey DeploymentCompositionEvidence
  -> Maybe DeploymentQualification
  -> DeploymentAuthorityPolicy
  -> Either DeploymentAuthorityError DeploymentAuthorityGrant
issueDeploymentAuthority current plan domainEvidence compositionEvidence maybeQualification policy = do
  mapLeft DeploymentAuthorityQualificationError $
    checkDeploymentQualification
      current plan domainEvidence compositionEvidence maybeQualification
  qualification <- requireQualification maybeQualification
  validateAuthorityPolicy plan qualification policy
  Right (makeGrant current qualification policy)

checkDeploymentAuthorityGrant
  :: Integer
  -> DeploymentPlan
  -> Map.Map DeploymentEvidenceKey DeploymentDomainEvidence
  -> Map.Map DeploymentCompositionEvidenceKey DeploymentCompositionEvidence
  -> Maybe DeploymentQualification
  -> DeploymentAuthorityPolicy
  -> DeploymentAuthorityGrant
  -> Either DeploymentAuthorityError ()
checkDeploymentAuthorityGrant current plan domainEvidence compositionEvidence maybeQualification policy grant = do
  mapLeft DeploymentAuthorityQualificationError $
    checkDeploymentQualification
      current plan domainEvidence compositionEvidence maybeQualification
  qualification <- requireQualification maybeQualification
  validateAuthorityPolicy plan qualification policy
  unless
    (deploymentAuthorityGrantPolicyRevision grant == deploymentAuthorityPolicyRevision policy) $
    Left (DeploymentAuthorityGrantPolicyMismatch
      (deploymentAuthorityPolicyRevision policy)
      (deploymentAuthorityGrantPolicyRevision grant))
  unless
    (deploymentAuthorityGrantQualificationId grant == deploymentQualificationId qualification) $
    Left (DeploymentAuthorityGrantQualificationMismatch
      (deploymentQualificationId qualification)
      (deploymentAuthorityGrantQualificationId grant))
  unless (deploymentAuthorityGrantClaim grant == deploymentAuthorityRequiredClaim policy) $
    Left (DeploymentAuthorityGrantClaimMismatch
      (deploymentAuthorityRequiredClaim policy)
      (deploymentAuthorityGrantClaim grant))
  unless (deploymentAuthorityGrantAction grant == deploymentAuthorityAction policy) $
    Left (DeploymentAuthorityGrantActionMismatch
      (deploymentAuthorityAction policy)
      (deploymentAuthorityGrantAction grant))
  unless (deploymentAuthorityGrantResource grant == deploymentAuthorityResource policy) $
    Left (DeploymentAuthorityGrantResourceMismatch
      (deploymentAuthorityResource policy)
      (deploymentAuthorityGrantResource grant))
  when (current < deploymentAuthorityGrantValidFrom grant) $
    Left (DeploymentAuthorityGrantNotYetValid
      current (deploymentAuthorityGrantValidFrom grant))
  when (current > deploymentAuthorityGrantValidUntil grant) $
    Left (DeploymentAuthorityGrantExpired
      current (deploymentAuthorityGrantValidUntil grant))
  unless
    (deploymentAuthorityGrantValidUntil grant == deploymentQualificationValidUntil qualification) $
    Left (DeploymentAuthorityGrantValidityMismatch
      (deploymentQualificationValidUntil qualification)
      (deploymentAuthorityGrantValidUntil grant))
  let expectedId = deriveDeploymentAuthorityGrantId grant
  unless (deploymentAuthorityGrantId grant == expectedId) $
    Left (DeploymentAuthorityGrantIdentityMismatch
      expectedId (deploymentAuthorityGrantId grant))

validateAuthorityPolicy
  :: DeploymentPlan
  -> DeploymentQualification
  -> DeploymentAuthorityPolicy
  -> Either DeploymentAuthorityError ()
validateAuthorityPolicy plan qualification policy = do
  when
    (Text.null
      (unDeploymentAuthorityPolicyRevision (deploymentAuthorityPolicyRevision policy))) $
    Left DeploymentAuthorityPolicyRevisionEmpty
  when (Text.null (deploymentAuthorityAction policy)) $
    Left DeploymentAuthorityActionEmpty
  when (Text.null (deploymentAuthorityResource policy)) $
    Left DeploymentAuthorityResourceEmpty
  unless
    (deploymentAuthorityRequiredDeploymentPolicy policy == deploymentPlanPolicy plan) $
    Left (DeploymentAuthorityDeploymentPolicyMismatch
      (deploymentPlanPolicy plan)
      (deploymentAuthorityRequiredDeploymentPolicy policy))
  unless
    (Map.member (deploymentAuthorityRequiredClaim policy) (deploymentPlanClaimDomains plan)) $
    Left (DeploymentAuthorityClaimNotPlanned
      (deploymentAuthorityRequiredClaim policy))
  unless
    (Set.member
      (deploymentAuthorityRequiredClaim policy)
      (deploymentQualificationCoveredClaims qualification)) $
    Left (DeploymentAuthorityClaimNotQualified
      (deploymentAuthorityRequiredClaim policy))

makeGrant
  :: Integer
  -> DeploymentQualification
  -> DeploymentAuthorityPolicy
  -> DeploymentAuthorityGrant
makeGrant current qualification policy = provisional
  { deploymentAuthorityGrantId = deriveDeploymentAuthorityGrantId provisional }
  where
    provisional = DeploymentAuthorityGrant
      { deploymentAuthorityGrantId = DeploymentAuthorityGrantId "pending"
      , deploymentAuthorityGrantPolicyRevision = deploymentAuthorityPolicyRevision policy
      , deploymentAuthorityGrantQualificationId = deploymentQualificationId qualification
      , deploymentAuthorityGrantClaim = deploymentAuthorityRequiredClaim policy
      , deploymentAuthorityGrantAction = deploymentAuthorityAction policy
      , deploymentAuthorityGrantResource = deploymentAuthorityResource policy
      , deploymentAuthorityGrantValidFrom = current
      , deploymentAuthorityGrantValidUntil = deploymentQualificationValidUntil qualification
      }

requireQualification
  :: Maybe DeploymentQualification
  -> Either DeploymentAuthorityError DeploymentQualification
requireQualification maybeQualification = case maybeQualification of
  Nothing -> Left (DeploymentAuthorityQualificationError DeploymentQualificationMissing)
  Just qualification -> Right qualification

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
