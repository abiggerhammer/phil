{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.DeploymentQualification
import Phil.Assurance.DeploymentQualificationCertification
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
    [ test "production qualification success is exact-kernel accepted" validCertificationAccepts
    , test "valid composite qualification reflects all thirteen facts" validFactsAreAllTrue
    , test "one reflected semantic disagreement fails closed" reflectedDisagreementRejects
    , test "missing qualification fails the extracted availability gate" missingAvailabilityRejects
    , test "native qualification diagnostics retain precedence" nativeDiagnosticPrecedence
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validCertificationAccepts :: Either String ()
validCertificationAccepts =
  mapLeft show $ verifyDeploymentQualificationCertification
    currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
    (Just deploymentQualification)

validFactsAreAllTrue :: Either String ()
validFactsAreAllTrue =
  let facts = validFacts
  in assert (allFactsTrue facts) ("valid qualification reflected a false fact: " <> show facts)

reflectedDisagreementRejects :: Either String ()
reflectedDisagreementRejects =
  let facts = validFacts { kernelPolicyExact = False }
  in case verifyDeploymentQualificationKernelFacts True facts of
    Left (DeploymentQualificationCertificationKernelDisagreement rejected) ->
      assert (rejected == facts) "kernel disagreement lost exact reflected facts"
    other -> Left ("semantic disagreement did not fail closed: " <> show other)

missingAvailabilityRejects :: Either String ()
missingAvailabilityRejects =
  case verifyDeploymentQualificationKernelFacts False validFacts of
    Left (DeploymentQualificationCertificationKernelDisagreement rejected) ->
      assert (rejected == validFacts) "availability rejection lost exact reflected facts"
    other -> Left ("missing qualification presence passed availability gate: " <> show other)

nativeDiagnosticPrecedence :: Either String ()
nativeDiagnosticPrecedence =
  let bad = deploymentQualification { deploymentQualificationArtifact = otherArtifact }
  in case verifyDeploymentQualificationCertification
      currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry (Just bad) of
    Left (DeploymentQualificationCertificationNativeError
      (DeploymentQualificationArtifactMismatch expected actual)) ->
        assert (expected == artifact && actual == otherArtifact)
          "production wrapper changed native artifact mismatch payload"
    other -> Left ("native diagnostic was not preserved ahead of kernel gate: " <> show other)

validFacts :: DeploymentQualificationKernelFacts
validFacts = deploymentQualificationKernelFacts
  currentPoint deploymentPlan domainEvidenceRegistry compositionEvidenceRegistry
  deploymentQualification

allFactsTrue :: DeploymentQualificationKernelFacts -> Bool
allFactsTrue facts = and
  [ kernelTopologyIdentityValid facts
  , kernelLinksWellFormed facts
  , kernelClaimDomainsTotal facts
  , kernelClaimDomainsSound facts
  , kernelArtifactExact facts
  , kernelPolicyExact facts
  , kernelTopologyExact facts
  , kernelClaimSetExact facts
  , kernelIdentityValid facts
  , kernelQualificationCurrent facts
  , kernelEverySelectedDomainHasEvidence facts
  , kernelNoExtraDomainBinding facts
  , kernelCompositionEvidenceValid facts
  ]

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
