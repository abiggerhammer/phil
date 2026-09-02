{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
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
    [ test "DEP-003 exact deployment qualification closes selected plan" validQualificationAccepts
    , test "DEP-003 raw attestation evidence alone cannot discharge deployment claim" attestationOnlyRejects
    , test "DEP-003 qualification artifact must match selected deployment plan" artifactMismatchRejects
    , test "DEP-004 stale deployment qualification rejects" staleQualificationRejects
    , test "DEP-004 stale underlying domain evidence rejects" staleDomainEvidenceRejects
    , test "DEP-004 qualification cannot outlive underlying evidence" qualificationOutlivesEvidenceRejects
    , test "DEP-005 composite topology requires explicit composition evidence" missingCompositionRejects
    , test "DEP-005 independent attestations cannot form Frankenstein topology" frankensteinTopologyRejects
    , test "DEP-005 every selected deployment domain needs exact evidence" missingDomainEvidenceRejects
    , test "DEP-005 domain evidence must cover claims assigned to that domain" missingDomainClaimRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validQualificationAccepts :: Either String ()
validQualificationAccepts =
  mapLeft show $ checkDeploymentQualification
    currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification)

attestationOnlyRejects :: Either String ()
attestationOnlyRejects =
  case checkDeploymentQualification
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry Nothing of
    Left DeploymentQualificationMissing -> Right ()
    other -> Left ("raw deployment evidence closed a claim without qualification: " <> show other)

artifactMismatchRejects :: Either String ()
artifactMismatchRejects =
  let bad = deploymentQualification
        { deploymentQualificationArtifact = otherArtifact }
  in case checkDeploymentQualification
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry (Just bad) of
    Left (DeploymentQualificationArtifactMismatch expected actual) ->
      assert (expected == artifact && actual == otherArtifact)
        "artifact mismatch rejection lost exact artifact identities"
    other -> Left ("mismatched qualification artifact was accepted: " <> show other)

staleQualificationRejects :: Either String ()
staleQualificationRejects =
  case checkDeploymentQualification
      201 deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
      (Just deploymentQualification) of
    Left (DeploymentQualificationStale point validFrom validUntil) ->
      assert (point == 201 && validFrom == 120 && validUntil == 180)
        "stale qualification rejection lost exact validity interval"
    other -> Left ("stale deployment qualification was accepted: " <> show other)

staleDomainEvidenceRejects :: Either String ()
staleDomainEvidenceRejects =
  let staleGpu = gpuEvidence { deploymentDomainEvidenceValidUntil = 140 }
      registry = Map.insert gpuEvidenceKey staleGpu domainEvidenceRegistry
  in case checkDeploymentQualification
      currentPoint deploymentPlan registry compositionEvidenceRegistry
      (Just deploymentQualification) of
    Left (DeploymentDomainEvidenceStale key point validFrom validUntil) ->
      assert
        ( key == gpuEvidenceKey
          && point == currentPoint
          && validFrom == 100
          && validUntil == 140
        )
        "stale domain evidence rejection lost exact evidence/validity identity"
    other -> Left ("stale domain evidence was accepted: " <> show other)

qualificationOutlivesEvidenceRejects :: Either String ()
qualificationOutlivesEvidenceRejects =
  let tooWide = makeDeploymentQualification deploymentPlan domainEvidenceBindings
        (Just compositionEvidenceKey) 90 180
  in case checkDeploymentQualification
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
      (Just tooWide) of
    Left (DeploymentQualificationOutlivesDomainEvidence key innerFrom innerUntil outerFrom outerUntil) ->
      assert
        ( key == cpuEvidenceKey
          && innerFrom == 90
          && innerUntil == 180
          && outerFrom == 100
          && outerUntil == 200
        )
        "qualification/evidence interval rejection lost exact bounds"
    other -> Left ("qualification outliving evidence was accepted: " <> show other)

missingCompositionRejects :: Either String ()
missingCompositionRejects =
  let bad = makeDeploymentQualification deploymentPlan domainEvidenceBindings Nothing 120 180
  in case checkDeploymentQualification
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry (Just bad) of
    Left (DeploymentCompositionEvidenceMissing revision) ->
      assert (revision == deploymentTopologyRevision topology)
        "missing composition rejection lost exact topology revision"
    other -> Left ("composite topology was accepted without composition evidence: " <> show other)

frankensteinTopologyRejects :: Either String ()
frankensteinTopologyRejects =
  let disconnected = compositionEvidence
        { deploymentCompositionEvidenceLinks = Set.empty }
      registry = Map.singleton compositionEvidenceKey disconnected
  in case checkDeploymentQualification
      currentPoint deploymentPlan domainEvidenceRegistry registry
      (Just deploymentQualification) of
    Left (DeploymentCompositionEvidenceLinkMismatch key expected actual) ->
      assert
        ( key == compositionEvidenceKey
          && expected == Set.singleton cpuToGpuLink
          && Set.null actual
        )
        "Frankenstein-topology rejection lost exact composition/link identity"
    other -> Left ("independent domain attestations were accepted as composite topology: " <> show other)

missingDomainEvidenceRejects :: Either String ()
missingDomainEvidenceRejects =
  let incompleteBindings = Map.singleton cpuDomain cpuEvidenceKey
      bad = makeDeploymentQualification deploymentPlan incompleteBindings
        (Just compositionEvidenceKey) 120 180
  in case checkDeploymentQualification
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry (Just bad) of
    Left (DeploymentDomainEvidenceDomainSetMismatch expected actual) ->
      assert
        ( expected == Set.fromList [cpuDomain, gpuDomain]
          && actual == Set.singleton cpuDomain
        )
        "missing-domain rejection lost exact topology domain set"
    other -> Left ("qualification omitted one deployment domain: " <> show other)

missingDomainClaimRejects :: Either String ()
missingDomainClaimRejects =
  let incompleteGpu = gpuEvidence { deploymentDomainEvidenceClaims = Set.empty }
      registry = Map.insert gpuEvidenceKey incompleteGpu domainEvidenceRegistry
  in case checkDeploymentQualification
      currentPoint deploymentPlan registry compositionEvidenceRegistry
      (Just deploymentQualification) of
    Left (DeploymentDomainEvidenceMissingClaims key missing) ->
      assert (key == gpuEvidenceKey && missing == Set.singleton crossDomainClaim)
        "domain-claim rejection lost exact evidence/claim identity"
    other -> Left ("domain evidence omitted a required claim: " <> show other)

currentPoint :: Integer
currentPoint = 150

artifact, otherArtifact :: ArtifactIdentity
artifact = ArtifactIdentity
  { artifactReference = ArtifactRef "artifact://phil/demo/deployable"
  , artifactDigest = Digest "sha256.demo-deployable.v1"
  }
otherArtifact = ArtifactIdentity
  { artifactReference = ArtifactRef "artifact://phil/demo/other"
  , artifactDigest = Digest "sha256.other.v1"
  }

policy :: DeploymentPolicyRevision
policy = DeploymentPolicyRevision "deployment.policy.checked-composite.v1"

cpuDomain, gpuDomain :: DeploymentDomainKey
cpuDomain = DeploymentDomainKey "domain.host.cpu"
gpuDomain = DeploymentDomainKey "domain.accelerator.gpu0"

cpuToGpuLink :: DeploymentLink
cpuToGpuLink = DeploymentLink
  { deploymentLinkFrom = cpuDomain
  , deploymentLinkTo = gpuDomain
  , deploymentLinkRelation = "checked-buffer-transfer"
  }

topology :: DeploymentTopology
topology = makeDeploymentTopology
  (Map.fromList
    [ ("host-runtime", cpuDomain)
    , ("accelerator-stage", gpuDomain)
    ])
  (Set.singleton cpuToGpuLink)

hostClaim, crossDomainClaim :: RevisionId
hostClaim = RevisionId "claim.deployment.host-runtime.v1"
crossDomainClaim = RevisionId "claim.deployment.cross-domain-transfer.v1"

deploymentPlan :: DeploymentPlan
deploymentPlan = DeploymentPlan
  { deploymentPlanArtifact = artifact
  , deploymentPlanPolicy = policy
  , deploymentPlanTopology = topology
  , deploymentPlanClaimDomains = Map.fromList
      [ (hostClaim, Set.singleton cpuDomain)
      , (crossDomainClaim, Set.fromList [cpuDomain, gpuDomain])
      ]
  }

cpuEvidenceKey, gpuEvidenceKey :: DeploymentEvidenceKey
cpuEvidenceKey = DeploymentEvidenceKey "attestation.host.cpu.v1"
gpuEvidenceKey = DeploymentEvidenceKey "attestation.gpu0.v1"

cpuEvidence, gpuEvidence :: DeploymentDomainEvidence
cpuEvidence = DeploymentDomainEvidence
  { deploymentDomainEvidenceKey = cpuEvidenceKey
  , deploymentDomainEvidenceArtifact = artifact
  , deploymentDomainEvidencePolicy = policy
  , deploymentDomainEvidenceDomain = cpuDomain
  , deploymentDomainEvidenceValidFrom = 100
  , deploymentDomainEvidenceValidUntil = 200
  , deploymentDomainEvidenceClaims = Set.fromList [hostClaim, crossDomainClaim]
  }
gpuEvidence = DeploymentDomainEvidence
  { deploymentDomainEvidenceKey = gpuEvidenceKey
  , deploymentDomainEvidenceArtifact = artifact
  , deploymentDomainEvidencePolicy = policy
  , deploymentDomainEvidenceDomain = gpuDomain
  , deploymentDomainEvidenceValidFrom = 100
  , deploymentDomainEvidenceValidUntil = 200
  , deploymentDomainEvidenceClaims = Set.singleton crossDomainClaim
  }

domainEvidenceBindings :: Map.Map DeploymentDomainKey DeploymentEvidenceKey
domainEvidenceBindings = Map.fromList
  [ (cpuDomain, cpuEvidenceKey)
  , (gpuDomain, gpuEvidenceKey)
  ]

domainEvidenceRegistry :: Map.Map DeploymentEvidenceKey DeploymentDomainEvidence
domainEvidenceRegistry = Map.fromList
  [ (cpuEvidenceKey, cpuEvidence)
  , (gpuEvidenceKey, gpuEvidence)
  ]

compositionEvidenceKey :: DeploymentCompositionEvidenceKey
compositionEvidenceKey = DeploymentCompositionEvidenceKey "composition.host-gpu.v1"

compositionEvidence :: DeploymentCompositionEvidence
compositionEvidence = DeploymentCompositionEvidence
  { deploymentCompositionEvidenceKey = compositionEvidenceKey
  , deploymentCompositionEvidenceArtifact = artifact
  , deploymentCompositionEvidencePolicy = policy
  , deploymentCompositionEvidenceTopologyRevision = deploymentTopologyRevision topology
  , deploymentCompositionEvidenceDomains = Set.fromList [cpuDomain, gpuDomain]
  , deploymentCompositionEvidenceLinks = Set.singleton cpuToGpuLink
  , deploymentCompositionEvidenceValidFrom = 110
  , deploymentCompositionEvidenceValidUntil = 190
  , deploymentCompositionEvidenceClaims = Set.fromList [hostClaim, crossDomainClaim]
  }

compositionEvidenceRegistry
  :: Map.Map DeploymentCompositionEvidenceKey DeploymentCompositionEvidence
compositionEvidenceRegistry = Map.singleton compositionEvidenceKey compositionEvidence

deploymentQualification :: DeploymentQualification
deploymentQualification = makeDeploymentQualification deploymentPlan domainEvidenceBindings
  (Just compositionEvidenceKey) 120 180

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
