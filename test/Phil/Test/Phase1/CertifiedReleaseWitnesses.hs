{-# LANGUAGE OverloadedStrings #-}

module Phil.Test.Phase1.CertifiedReleaseWitnesses
  ( certifyConventionalFixture
  , conventionalReleaseProfile
  , conventionalTrust
  , fixtureLLVMArtifact
  ) where

import qualified Data.Set as Set
import Phil.Assurance.Types (AssuranceManifest (..))
import Phil.LLVM.IR (LLVMArtifact)
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.LLVM.Phase0 (phase0LLVMTarget)
import Phil.Systems.IR (SystemsArtifact)
import Phil.Systems.Phase1Stage (phase1StageSystemsArtifact)
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , concreteSubjectStage
  )
import Phil.Systems.SubjectCorrespondence (SubjectStageBundle (..))
import Phil.Test.Phase1.ManifestWitnesses
import Phil.Verification.CertifiedRelease

certifyConventionalFixture
  :: RealManifestFixture
  -> Either CertifiedReleaseError CertifiedReleaseArtifact
certifyConventionalFixture fixture = certifyReleaseArtifact
  (conventionalReleaseProfile manifest)
  (realFixtureContext fixture)
  (realFixtureLedger fixture)
  manifest
  (realFixtureStage fixture)
  (fixtureLLVMArtifact fixture)
  conventionalTrust
  where
    manifest = realFixtureManifest fixture

fixtureLLVMArtifact :: RealManifestFixture -> LLVMArtifact
fixtureLLVMArtifact = lowerSystemsConservative phase0LLVMTarget
  . stageSystemsArtifact
  . realFixtureStage

conventionalReleaseProfile :: AssuranceManifest -> CertifiedReleaseProfile
conventionalReleaseProfile manifest = CertifiedReleaseProfile
  { releaseProfileRevision = ReleaseProfileRevision
      "phase1.int005.conventional-x86_64-linux.v1"
  , releaseProfileManifestTarget = manifestTarget manifest
  , releaseProfileManifestCompilationProfile = manifestCompilationProfile manifest
  , releaseProfileLLVMTarget = phase0LLVMTarget
  , releaseProfileRequiredTrustKinds = Set.fromList
      [ CompilerCheckerTrust
      , LLVMToolchainTrust
      , RuntimeTrust
      , ProviderTrust
      , ExternalCheckerTrust
      , TargetAssumptionTrust
      ]
  }

stageSystemsArtifact :: StageClosureBundle -> SystemsArtifact
stageSystemsArtifact = phase1StageSystemsArtifact
  . subjectStageBase
  . concreteSubjectStage
  . stageClosureConcrete

conventionalTrust :: [ReleaseTrustBoundary]
conventionalTrust =
  [ trust "compiler-checker" CompilerCheckerTrust
      "Phil Haskell compiler/checker" "phase1-current"
      "first implementation remains trusted until Phase 2"
  , trust "llvm-toolchain" LLVMToolchainTrust
      "LLVM assembler/linker and clang" "LLVM 18.x"
      "conventional native emission and link toolchain"
  , trust "runtime" RuntimeTrust
      "Phil conventional host runtime" "phase1-runtime-v1"
      "runtime behavior below checked Phil/Systems contracts"
  , trust "providers" ProviderTrust
      "qualified conventional providers" "phase1-provider-set-v1"
      "provider implementations remain trusted at their declared qualification boundaries"
  , trust "external-checkers" ExternalCheckerTrust
      "external proof/certificate checkers" "phase1-certified-checker-set-v1"
      "accepted external evidence depends on the named competent checkers"
  , trust "target-assumptions" TargetAssumptionTrust
      "x86_64 Linux target assumptions" "phase1-x86_64-linux-v1"
      "selected conventional ABI/tool/runtime assumptions"
  ]
  where
    trust ident kind name revision basis = ReleaseTrustBoundary
      { releaseTrustBoundaryId = ReleaseTrustBoundaryId ident
      , releaseTrustKind = kind
      , releaseTrustName = name
      , releaseTrustRevision = revision
      , releaseTrustBasis = basis
      }
