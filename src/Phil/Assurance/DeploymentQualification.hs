{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.DeploymentQualification
  ( DeploymentPolicyRevision (..)
  , DeploymentDomainKey (..)
  , DeploymentEvidenceKey (..)
  , DeploymentCompositionEvidenceKey (..)
  , DeploymentTopologyRevision (..)
  , DeploymentQualificationId (..)
  , DeploymentLink (..)
  , DeploymentTopology (..)
  , DeploymentPlan (..)
  , DeploymentDomainEvidence (..)
  , DeploymentCompositionEvidence (..)
  , DeploymentQualification (..)
  , DeploymentQualificationError (..)
  , deriveDeploymentTopologyRevision
  , makeDeploymentTopology
  , deriveDeploymentQualificationId
  , makeDeploymentQualification
  , checkDeploymentQualification
  ) where

import Control.Monad (forM_, unless, when)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( ArtifactIdentity (..)
  , ArtifactRef (..)
  , Digest (..)
  , RevisionId (..)
  , digestText
  )

newtype DeploymentPolicyRevision = DeploymentPolicyRevision
  { unDeploymentPolicyRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype DeploymentDomainKey = DeploymentDomainKey
  { unDeploymentDomainKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype DeploymentEvidenceKey = DeploymentEvidenceKey
  { unDeploymentEvidenceKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype DeploymentCompositionEvidenceKey = DeploymentCompositionEvidenceKey
  { unDeploymentCompositionEvidenceKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype DeploymentTopologyRevision = DeploymentTopologyRevision
  { unDeploymentTopologyRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype DeploymentQualificationId = DeploymentQualificationId
  { unDeploymentQualificationId :: Text
  }
  deriving (Eq, Ord, Show)

data DeploymentLink = DeploymentLink
  { deploymentLinkFrom :: DeploymentDomainKey
  , deploymentLinkTo :: DeploymentDomainKey
  , deploymentLinkRelation :: Text
  }
  deriving (Eq, Ord, Show)

data DeploymentTopology = DeploymentTopology
  { deploymentTopologyRevision :: DeploymentTopologyRevision
  , deploymentTopologyComponentDomains :: Map Text DeploymentDomainKey
  , deploymentTopologyLinks :: Set DeploymentLink
  }
  deriving (Eq, Show)

data DeploymentPlan = DeploymentPlan
  { deploymentPlanArtifact :: ArtifactIdentity
  , deploymentPlanPolicy :: DeploymentPolicyRevision
  , deploymentPlanTopology :: DeploymentTopology
  , deploymentPlanClaimDomains :: Map RevisionId (Set DeploymentDomainKey)
  }
  deriving (Eq, Show)

data DeploymentDomainEvidence = DeploymentDomainEvidence
  { deploymentDomainEvidenceKey :: DeploymentEvidenceKey
  , deploymentDomainEvidenceArtifact :: ArtifactIdentity
  , deploymentDomainEvidencePolicy :: DeploymentPolicyRevision
  , deploymentDomainEvidenceDomain :: DeploymentDomainKey
  , deploymentDomainEvidenceValidFrom :: Integer
  , deploymentDomainEvidenceValidUntil :: Integer
  , deploymentDomainEvidenceClaims :: Set RevisionId
  }
  deriving (Eq, Show)

data DeploymentCompositionEvidence = DeploymentCompositionEvidence
  { deploymentCompositionEvidenceKey :: DeploymentCompositionEvidenceKey
  , deploymentCompositionEvidenceArtifact :: ArtifactIdentity
  , deploymentCompositionEvidencePolicy :: DeploymentPolicyRevision
  , deploymentCompositionEvidenceTopologyRevision :: DeploymentTopologyRevision
  , deploymentCompositionEvidenceDomains :: Set DeploymentDomainKey
  , deploymentCompositionEvidenceLinks :: Set DeploymentLink
  , deploymentCompositionEvidenceValidFrom :: Integer
  , deploymentCompositionEvidenceValidUntil :: Integer
  , deploymentCompositionEvidenceClaims :: Set RevisionId
  }
  deriving (Eq, Show)

data DeploymentQualification = DeploymentQualification
  { deploymentQualificationId :: DeploymentQualificationId
  , deploymentQualificationArtifact :: ArtifactIdentity
  , deploymentQualificationPolicy :: DeploymentPolicyRevision
  , deploymentQualificationTopologyRevision :: DeploymentTopologyRevision
  , deploymentQualificationCoveredClaims :: Set RevisionId
  , deploymentQualificationDomainEvidence :: Map DeploymentDomainKey DeploymentEvidenceKey
  , deploymentQualificationCompositionEvidence :: Maybe DeploymentCompositionEvidenceKey
  , deploymentQualificationValidFrom :: Integer
  , deploymentQualificationValidUntil :: Integer
  }
  deriving (Eq, Show)

data DeploymentQualificationError
  = DeploymentQualificationMissing
  | DeploymentPlanTopologyIdentityMismatch DeploymentTopologyRevision DeploymentTopologyRevision
  | DeploymentPlanLinkUnknownDomain DeploymentLink
  | DeploymentPlanClaimWithoutDomain RevisionId
  | DeploymentPlanClaimUnknownDomain RevisionId (Set DeploymentDomainKey)
  | DeploymentQualificationArtifactMismatch ArtifactIdentity ArtifactIdentity
  | DeploymentQualificationPolicyMismatch DeploymentPolicyRevision DeploymentPolicyRevision
  | DeploymentQualificationTopologyMismatch DeploymentTopologyRevision DeploymentTopologyRevision
  | DeploymentQualificationClaimSetMismatch (Set RevisionId) (Set RevisionId)
  | DeploymentQualificationInvalidValidity Integer Integer
  | DeploymentQualificationStale Integer Integer Integer
  | DeploymentQualificationIdentityMismatch DeploymentQualificationId DeploymentQualificationId
  | DeploymentDomainEvidenceDomainSetMismatch (Set DeploymentDomainKey) (Set DeploymentDomainKey)
  | DeploymentDomainEvidenceUnknown DeploymentDomainKey DeploymentEvidenceKey
  | DeploymentDomainEvidenceMapKeyMismatch DeploymentEvidenceKey DeploymentEvidenceKey
  | DeploymentDomainEvidenceDomainMismatch DeploymentEvidenceKey DeploymentDomainKey DeploymentDomainKey
  | DeploymentDomainEvidenceArtifactMismatch DeploymentEvidenceKey ArtifactIdentity ArtifactIdentity
  | DeploymentDomainEvidencePolicyMismatch DeploymentEvidenceKey DeploymentPolicyRevision DeploymentPolicyRevision
  | DeploymentDomainEvidenceInvalidValidity DeploymentEvidenceKey Integer Integer
  | DeploymentDomainEvidenceStale DeploymentEvidenceKey Integer Integer Integer
  | DeploymentQualificationOutlivesDomainEvidence DeploymentEvidenceKey Integer Integer Integer Integer
  | DeploymentDomainEvidenceMissingClaims DeploymentEvidenceKey (Set RevisionId)
  | DeploymentCompositionEvidenceMissing DeploymentTopologyRevision
  | DeploymentCompositionEvidenceUnexpected DeploymentCompositionEvidenceKey
  | DeploymentCompositionEvidenceUnknown DeploymentCompositionEvidenceKey
  | DeploymentCompositionEvidenceMapKeyMismatch DeploymentCompositionEvidenceKey DeploymentCompositionEvidenceKey
  | DeploymentCompositionEvidenceArtifactMismatch DeploymentCompositionEvidenceKey ArtifactIdentity ArtifactIdentity
  | DeploymentCompositionEvidencePolicyMismatch DeploymentCompositionEvidenceKey DeploymentPolicyRevision DeploymentPolicyRevision
  | DeploymentCompositionEvidenceTopologyMismatch DeploymentCompositionEvidenceKey DeploymentTopologyRevision DeploymentTopologyRevision
  | DeploymentCompositionEvidenceDomainMismatch DeploymentCompositionEvidenceKey (Set DeploymentDomainKey) (Set DeploymentDomainKey)
  | DeploymentCompositionEvidenceLinkMismatch DeploymentCompositionEvidenceKey (Set DeploymentLink) (Set DeploymentLink)
  | DeploymentCompositionEvidenceInvalidValidity DeploymentCompositionEvidenceKey Integer Integer
  | DeploymentCompositionEvidenceStale DeploymentCompositionEvidenceKey Integer Integer Integer
  | DeploymentQualificationOutlivesCompositionEvidence DeploymentCompositionEvidenceKey Integer Integer Integer Integer
  | DeploymentCompositionEvidenceMissingClaims DeploymentCompositionEvidenceKey (Set RevisionId)
  deriving (Eq, Show)

deriveDeploymentTopologyRevision
  :: Map Text DeploymentDomainKey
  -> Set DeploymentLink
  -> DeploymentTopologyRevision
deriveDeploymentTopologyRevision assignments links = DeploymentTopologyRevision
  ("deployment.topology.sha256." <> unDigest (digestText payload))
  where
    payload = Text.intercalate "|"
      [ "assignments=" <> Text.intercalate ","
          [ component <> "=>" <> unDeploymentDomainKey domain
          | (component, domain) <- Map.toAscList assignments
          ]
      , "links=" <> Text.intercalate ","
          [ renderLink link
          | link <- Set.toAscList links
          ]
      ]

makeDeploymentTopology
  :: Map Text DeploymentDomainKey
  -> Set DeploymentLink
  -> DeploymentTopology
makeDeploymentTopology assignments links = DeploymentTopology
  { deploymentTopologyRevision = deriveDeploymentTopologyRevision assignments links
  , deploymentTopologyComponentDomains = assignments
  , deploymentTopologyLinks = links
  }

deriveDeploymentQualificationId
  :: DeploymentQualification
  -> DeploymentQualificationId
deriveDeploymentQualificationId qualification = DeploymentQualificationId
  ("deployment.qualification.sha256." <> unDigest (digestText payload))
  where
    artifact = deploymentQualificationArtifact qualification
    payload = Text.intercalate "|"
      [ "artifact_ref=" <> unArtifactRef (artifactReference artifact)
      , "artifact_digest=" <> unDigest (artifactDigest artifact)
      , "policy=" <> unDeploymentPolicyRevision (deploymentQualificationPolicy qualification)
      , "topology=" <> unDeploymentTopologyRevision (deploymentQualificationTopologyRevision qualification)
      , "claims=" <> Text.intercalate ","
          (map unRevisionId (Set.toAscList (deploymentQualificationCoveredClaims qualification)))
      , "domain_evidence=" <> Text.intercalate ","
          [ unDeploymentDomainKey domain <> "=>" <> unDeploymentEvidenceKey evidenceKey
          | (domain, evidenceKey) <- Map.toAscList (deploymentQualificationDomainEvidence qualification)
          ]
      , "composition=" <> maybe "none" unDeploymentCompositionEvidenceKey
          (deploymentQualificationCompositionEvidence qualification)
      , "valid_from=" <> Text.pack (show (deploymentQualificationValidFrom qualification))
      , "valid_until=" <> Text.pack (show (deploymentQualificationValidUntil qualification))
      ]

makeDeploymentQualification
  :: DeploymentPlan
  -> Map DeploymentDomainKey DeploymentEvidenceKey
  -> Maybe DeploymentCompositionEvidenceKey
  -> Integer
  -> Integer
  -> DeploymentQualification
makeDeploymentQualification plan domainEvidence composition validFrom validUntil =
  provisional
    { deploymentQualificationId = deriveDeploymentQualificationId provisional }
  where
    provisional = DeploymentQualification
      { deploymentQualificationId = DeploymentQualificationId "pending"
      , deploymentQualificationArtifact = deploymentPlanArtifact plan
      , deploymentQualificationPolicy = deploymentPlanPolicy plan
      , deploymentQualificationTopologyRevision =
          deploymentTopologyRevision (deploymentPlanTopology plan)
      , deploymentQualificationCoveredClaims = Map.keysSet (deploymentPlanClaimDomains plan)
      , deploymentQualificationDomainEvidence = domainEvidence
      , deploymentQualificationCompositionEvidence = composition
      , deploymentQualificationValidFrom = validFrom
      , deploymentQualificationValidUntil = validUntil
      }

checkDeploymentQualification
  :: Integer
  -> DeploymentPlan
  -> Map DeploymentEvidenceKey DeploymentDomainEvidence
  -> Map DeploymentCompositionEvidenceKey DeploymentCompositionEvidence
  -> Maybe DeploymentQualification
  -> Either DeploymentQualificationError ()
checkDeploymentQualification current plan domainEvidenceRegistry compositionRegistry maybeQualification = do
  validatePlan
  qualification <- case maybeQualification of
    Nothing -> Left DeploymentQualificationMissing
    Just value -> Right value
  unless (deploymentQualificationArtifact qualification == deploymentPlanArtifact plan) $
    Left (DeploymentQualificationArtifactMismatch
      (deploymentPlanArtifact plan) (deploymentQualificationArtifact qualification))
  unless (deploymentQualificationPolicy qualification == deploymentPlanPolicy plan) $
    Left (DeploymentQualificationPolicyMismatch
      (deploymentPlanPolicy plan) (deploymentQualificationPolicy qualification))
  let expectedTopologyRevision = deploymentTopologyRevision topology
  unless (deploymentQualificationTopologyRevision qualification == expectedTopologyRevision) $
    Left (DeploymentQualificationTopologyMismatch
      expectedTopologyRevision (deploymentQualificationTopologyRevision qualification))
  let expectedClaims = Map.keysSet (deploymentPlanClaimDomains plan)
  unless (deploymentQualificationCoveredClaims qualification == expectedClaims) $
    Left (DeploymentQualificationClaimSetMismatch
      expectedClaims (deploymentQualificationCoveredClaims qualification))
  validateInterval
    DeploymentQualificationInvalidValidity
    (deploymentQualificationValidFrom qualification)
    (deploymentQualificationValidUntil qualification)
  unless (pointWithin current
      (deploymentQualificationValidFrom qualification)
      (deploymentQualificationValidUntil qualification)) $
    Left (DeploymentQualificationStale
      current
      (deploymentQualificationValidFrom qualification)
      (deploymentQualificationValidUntil qualification))
  let expectedQualificationId = deriveDeploymentQualificationId qualification
  unless (deploymentQualificationId qualification == expectedQualificationId) $
    Left (DeploymentQualificationIdentityMismatch
      expectedQualificationId (deploymentQualificationId qualification))
  validateDomainEvidence qualification
  validateCompositionEvidence qualification
  where
    topology = deploymentPlanTopology plan
    topologyDomains = Set.fromList (Map.elems (deploymentTopologyComponentDomains topology))
    expectedTopologyIdentity = deriveDeploymentTopologyRevision
      (deploymentTopologyComponentDomains topology)
      (deploymentTopologyLinks topology)

    validatePlan = do
      unless (deploymentTopologyRevision topology == expectedTopologyIdentity) $
        Left (DeploymentPlanTopologyIdentityMismatch
          expectedTopologyIdentity (deploymentTopologyRevision topology))
      forM_ (Set.toAscList (deploymentTopologyLinks topology)) $ \link ->
        unless
          ( Set.member (deploymentLinkFrom link) topologyDomains
            && Set.member (deploymentLinkTo link) topologyDomains
          ) $
          Left (DeploymentPlanLinkUnknownDomain link)
      forM_ (Map.toAscList (deploymentPlanClaimDomains plan)) $ \(claim, domains) -> do
        when (Set.null domains) $
          Left (DeploymentPlanClaimWithoutDomain claim)
        let unknown = Set.difference domains topologyDomains
        unless (Set.null unknown) $
          Left (DeploymentPlanClaimUnknownDomain claim unknown)

    validateDomainEvidence qualification = do
      let bindings = deploymentQualificationDomainEvidence qualification
      unless (Map.keysSet bindings == topologyDomains) $
        Left (DeploymentDomainEvidenceDomainSetMismatch
          topologyDomains (Map.keysSet bindings))
      forM_ (Map.toAscList bindings) $ \(domain, evidenceKey) -> do
        evidence <- case Map.lookup evidenceKey domainEvidenceRegistry of
          Nothing -> Left (DeploymentDomainEvidenceUnknown domain evidenceKey)
          Just value -> Right value
        unless (deploymentDomainEvidenceKey evidence == evidenceKey) $
          Left (DeploymentDomainEvidenceMapKeyMismatch
            evidenceKey (deploymentDomainEvidenceKey evidence))
        unless (deploymentDomainEvidenceDomain evidence == domain) $
          Left (DeploymentDomainEvidenceDomainMismatch
            evidenceKey domain (deploymentDomainEvidenceDomain evidence))
        unless (deploymentDomainEvidenceArtifact evidence == deploymentPlanArtifact plan) $
          Left (DeploymentDomainEvidenceArtifactMismatch
            evidenceKey (deploymentPlanArtifact plan) (deploymentDomainEvidenceArtifact evidence))
        unless (deploymentDomainEvidencePolicy evidence == deploymentPlanPolicy plan) $
          Left (DeploymentDomainEvidencePolicyMismatch
            evidenceKey (deploymentPlanPolicy plan) (deploymentDomainEvidencePolicy evidence))
        validateInterval
          (DeploymentDomainEvidenceInvalidValidity evidenceKey)
          (deploymentDomainEvidenceValidFrom evidence)
          (deploymentDomainEvidenceValidUntil evidence)
        unless (pointWithin current
            (deploymentDomainEvidenceValidFrom evidence)
            (deploymentDomainEvidenceValidUntil evidence)) $
          Left (DeploymentDomainEvidenceStale
            evidenceKey current
            (deploymentDomainEvidenceValidFrom evidence)
            (deploymentDomainEvidenceValidUntil evidence))
        unless (intervalWithin
            (deploymentQualificationValidFrom qualification)
            (deploymentQualificationValidUntil qualification)
            (deploymentDomainEvidenceValidFrom evidence)
            (deploymentDomainEvidenceValidUntil evidence)) $
          Left (DeploymentQualificationOutlivesDomainEvidence
            evidenceKey
            (deploymentQualificationValidFrom qualification)
            (deploymentQualificationValidUntil qualification)
            (deploymentDomainEvidenceValidFrom evidence)
            (deploymentDomainEvidenceValidUntil evidence))
        let requiredClaims = Set.fromList
              [ claim
              | (claim, domains) <- Map.toAscList (deploymentPlanClaimDomains plan)
              , Set.member domain domains
              ]
            missingClaims = Set.difference requiredClaims (deploymentDomainEvidenceClaims evidence)
        unless (Set.null missingClaims) $
          Left (DeploymentDomainEvidenceMissingClaims evidenceKey missingClaims)

    validateCompositionEvidence qualification
      | compositeTopology = case deploymentQualificationCompositionEvidence qualification of
          Nothing -> Left (DeploymentCompositionEvidenceMissing
            (deploymentTopologyRevision topology))
          Just evidenceKey -> validateComposition qualification evidenceKey
      | otherwise = case deploymentQualificationCompositionEvidence qualification of
          Nothing -> Right ()
          Just evidenceKey -> Left (DeploymentCompositionEvidenceUnexpected evidenceKey)

    compositeTopology = Set.size topologyDomains > 1 || not (Set.null (deploymentTopologyLinks topology))

    validateComposition qualification evidenceKey = do
      evidence <- case Map.lookup evidenceKey compositionRegistry of
        Nothing -> Left (DeploymentCompositionEvidenceUnknown evidenceKey)
        Just value -> Right value
      unless (deploymentCompositionEvidenceKey evidence == evidenceKey) $
        Left (DeploymentCompositionEvidenceMapKeyMismatch
          evidenceKey (deploymentCompositionEvidenceKey evidence))
      unless (deploymentCompositionEvidenceArtifact evidence == deploymentPlanArtifact plan) $
        Left (DeploymentCompositionEvidenceArtifactMismatch
          evidenceKey (deploymentPlanArtifact plan) (deploymentCompositionEvidenceArtifact evidence))
      unless (deploymentCompositionEvidencePolicy evidence == deploymentPlanPolicy plan) $
        Left (DeploymentCompositionEvidencePolicyMismatch
          evidenceKey (deploymentPlanPolicy plan) (deploymentCompositionEvidencePolicy evidence))
      unless (deploymentCompositionEvidenceTopologyRevision evidence == deploymentTopologyRevision topology) $
        Left (DeploymentCompositionEvidenceTopologyMismatch
          evidenceKey
          (deploymentTopologyRevision topology)
          (deploymentCompositionEvidenceTopologyRevision evidence))
      unless (deploymentCompositionEvidenceDomains evidence == topologyDomains) $
        Left (DeploymentCompositionEvidenceDomainMismatch
          evidenceKey topologyDomains (deploymentCompositionEvidenceDomains evidence))
      unless (deploymentCompositionEvidenceLinks evidence == deploymentTopologyLinks topology) $
        Left (DeploymentCompositionEvidenceLinkMismatch
          evidenceKey (deploymentTopologyLinks topology) (deploymentCompositionEvidenceLinks evidence))
      validateInterval
        (DeploymentCompositionEvidenceInvalidValidity evidenceKey)
        (deploymentCompositionEvidenceValidFrom evidence)
        (deploymentCompositionEvidenceValidUntil evidence)
      unless (pointWithin current
          (deploymentCompositionEvidenceValidFrom evidence)
          (deploymentCompositionEvidenceValidUntil evidence)) $
        Left (DeploymentCompositionEvidenceStale
          evidenceKey current
          (deploymentCompositionEvidenceValidFrom evidence)
          (deploymentCompositionEvidenceValidUntil evidence))
      unless (intervalWithin
          (deploymentQualificationValidFrom qualification)
          (deploymentQualificationValidUntil qualification)
          (deploymentCompositionEvidenceValidFrom evidence)
          (deploymentCompositionEvidenceValidUntil evidence)) $
        Left (DeploymentQualificationOutlivesCompositionEvidence
          evidenceKey
          (deploymentQualificationValidFrom qualification)
          (deploymentQualificationValidUntil qualification)
          (deploymentCompositionEvidenceValidFrom evidence)
          (deploymentCompositionEvidenceValidUntil evidence))
      let missingClaims = Set.difference
            (Map.keysSet (deploymentPlanClaimDomains plan))
            (deploymentCompositionEvidenceClaims evidence)
      unless (Set.null missingClaims) $
        Left (DeploymentCompositionEvidenceMissingClaims evidenceKey missingClaims)

validateInterval
  :: (Integer -> Integer -> DeploymentQualificationError)
  -> Integer
  -> Integer
  -> Either DeploymentQualificationError ()
validateInterval makeError validFrom validUntil =
  unless (validFrom <= validUntil) $
    Left (makeError validFrom validUntil)

pointWithin :: Integer -> Integer -> Integer -> Bool
pointWithin point validFrom validUntil =
  validFrom <= point && point <= validUntil

intervalWithin :: Integer -> Integer -> Integer -> Integer -> Bool
intervalWithin innerFrom innerUntil outerFrom outerUntil =
  outerFrom <= innerFrom && innerUntil <= outerUntil

renderLink :: DeploymentLink -> Text
renderLink link = Text.intercalate ":"
  [ unDeploymentDomainKey (deploymentLinkFrom link)
  , unDeploymentDomainKey (deploymentLinkTo link)
  , deploymentLinkRelation link
  ]
