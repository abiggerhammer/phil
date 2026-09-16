{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.CertifiedRelease
  ( ReleaseProfileRevision (..)
  , ReleaseTrustBoundaryId (..)
  , ReleaseTrustKind (..)
  , ReleaseTrustBoundary (..)
  , CertifiedReleaseProfile (..)
  , CertifiedReleaseArtifact
  , certifiedReleaseProfile
  , certifiedReleaseManifest
  , certifiedReleaseStageClosure
  , certifiedReleaseLLVMArtifact
  , certifiedReleaseTrustBoundaries
  , CertifiedReleaseError (..)
  , certifyReleaseArtifact
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( AssuranceLedger
  , AssuranceManifest (..)
  , Digest
  , VerificationContext
  )
import Phil.Assurance.Verify
  ( ManifestError
  , verifyManifest
  )
import Phil.LLVM.IR
  ( LLVMArtifact (..)
  , LLVMEmissionContract (..)
  , LLVMModule (..)
  , LLVMTargetProfile (..)
  , llvmModuleDigest
  , renderLLVMModule
  )
import Phil.Systems.IR
  ( loweringLedgerRoot
  , systemsArtifactDigest
  , systemsArtifactLoweringLedger
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , StageClosureVerificationError
  , concreteSubjectStage
  , verifyStageClosureBundle
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )

newtype ReleaseProfileRevision = ReleaseProfileRevision
  { unReleaseProfileRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ReleaseTrustBoundaryId = ReleaseTrustBoundaryId
  { unReleaseTrustBoundaryId :: Text
  }
  deriving (Eq, Ord, Show)

-- | Residual trust is classified rather than flattened into a generic
-- "compiler correctness" claim.  A concrete release profile chooses the exact
-- kind-domain that must be named for that profile.
data ReleaseTrustKind
  = CompilerCheckerTrust
  | LLVMToolchainTrust
  | RuntimeTrust
  | ProviderTrust
  | ExternalCheckerTrust
  | TargetAssumptionTrust
  deriving (Eq, Ord, Show)

data ReleaseTrustBoundary = ReleaseTrustBoundary
  { releaseTrustBoundaryId :: ReleaseTrustBoundaryId
  , releaseTrustKind :: ReleaseTrustKind
  , releaseTrustName :: Text
  , releaseTrustRevision :: Text
  , releaseTrustBasis :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact conventional release profile.  The assurance target/profile labels
-- and LLVM target are independent coordinates because neither is permitted to
-- stand in for the other.  The required trust-kind domain is explicit profile
-- data, so a release cannot silently omit a category that its profile declares
-- trusted.
data CertifiedReleaseProfile = CertifiedReleaseProfile
  { releaseProfileRevision :: ReleaseProfileRevision
  , releaseProfileManifestTarget :: Text
  , releaseProfileManifestCompilationProfile :: Text
  , releaseProfileLLVMTarget :: LLVMTargetProfile
  , releaseProfileRequiredTrustKinds :: Set ReleaseTrustKind
  }
  deriving (Eq, Ord, Show)

-- | One exact certified-release envelope.  Construction is intentionally
-- opaque: callers receive one only after the final assurance manifest, the
-- complete Systems StageClosure, the emitted LLVM artifact, target profile,
-- and residual TCB declaration agree on their shared identities.
data CertifiedReleaseArtifact = CertifiedReleaseArtifact
  CertifiedReleaseProfile
  AssuranceManifest
  StageClosureBundle
  LLVMArtifact
  (Map ReleaseTrustBoundaryId ReleaseTrustBoundary)
  deriving (Eq, Show)

certifiedReleaseProfile :: CertifiedReleaseArtifact -> CertifiedReleaseProfile
certifiedReleaseProfile (CertifiedReleaseArtifact profile _ _ _ _) = profile

certifiedReleaseManifest :: CertifiedReleaseArtifact -> AssuranceManifest
certifiedReleaseManifest (CertifiedReleaseArtifact _ manifest _ _ _) = manifest

certifiedReleaseStageClosure :: CertifiedReleaseArtifact -> StageClosureBundle
certifiedReleaseStageClosure (CertifiedReleaseArtifact _ _ stage _ _) = stage

certifiedReleaseLLVMArtifact :: CertifiedReleaseArtifact -> LLVMArtifact
certifiedReleaseLLVMArtifact (CertifiedReleaseArtifact _ _ _ artifact _) = artifact

certifiedReleaseTrustBoundaries
  :: CertifiedReleaseArtifact
  -> Map ReleaseTrustBoundaryId ReleaseTrustBoundary
certifiedReleaseTrustBoundaries
  (CertifiedReleaseArtifact _ _ _ _ boundaries) = boundaries

data CertifiedReleaseError
  = CertifiedReleaseEmptyProfileRevision
  | CertifiedReleaseEmptyManifestTarget
  | CertifiedReleaseEmptyManifestCompilationProfile
  | CertifiedReleaseEmptyRequiredTrustDomain
  | CertifiedReleaseManifestRejected ManifestError
  | CertifiedReleaseStageClosureRejected StageClosureVerificationError
  | CertifiedReleaseManifestTargetMismatch Text Text
  | CertifiedReleaseManifestCompilationProfileMismatch Text Text
  | CertifiedReleaseManifestImplementationDigestMismatch Digest Digest
  | CertifiedReleaseManifestLoweringLedgerRootMismatch Digest Digest
  | CertifiedReleaseLLVMSourceDigestMismatch Digest Digest
  | CertifiedReleaseLLVMTargetDigestMismatch Digest Digest
  | CertifiedReleaseLLVMTextMismatch
  | CertifiedReleaseLLVMTargetProfileMismatch LLVMTargetProfile LLVMTargetProfile
  | CertifiedReleaseDuplicateTrustBoundary ReleaseTrustBoundaryId
  | CertifiedReleaseEmptyTrustBoundaryId
  | CertifiedReleaseEmptyTrustName ReleaseTrustBoundaryId
  | CertifiedReleaseEmptyTrustRevision ReleaseTrustBoundaryId
  | CertifiedReleaseEmptyTrustBasis ReleaseTrustBoundaryId
  | CertifiedReleaseTrustKindDomainMismatch
      (Set ReleaseTrustKind)
      (Set ReleaseTrustKind)
  deriving (Eq, Show)

-- | Close the Phase-1 certified-release seam without inventing a second
-- assurance system.  The existing manifest verifier owns source assurance; the
-- existing StageClosure verifier owns complete Systems/realization/runtime/cost
-- closure.  This function only binds those accepted facts to one exact emitted
-- LLVM artifact and one explicitly named residual TCB profile.
certifyReleaseArtifact
  :: CertifiedReleaseProfile
  -> VerificationContext
  -> AssuranceLedger
  -> AssuranceManifest
  -> StageClosureBundle
  -> LLVMArtifact
  -> [ReleaseTrustBoundary]
  -> Either CertifiedReleaseError CertifiedReleaseArtifact
certifyReleaseArtifact profile context ledger manifest stage artifact trust = do
  validateProfile
  mapLeft CertifiedReleaseManifestRejected (verifyManifest context ledger manifest)
  mapLeft CertifiedReleaseStageClosureRejected (verifyStageClosureBundle stage)
  validateManifestProfile
  validateSystemsBinding
  validateLLVM
  boundaries <- validateTrustBoundaries trust
  pure (CertifiedReleaseArtifact profile manifest stage artifact boundaries)
  where
    validateProfile
      | blank (unReleaseProfileRevision (releaseProfileRevision profile)) =
          Left CertifiedReleaseEmptyProfileRevision
      | blank (releaseProfileManifestTarget profile) =
          Left CertifiedReleaseEmptyManifestTarget
      | blank (releaseProfileManifestCompilationProfile profile) =
          Left CertifiedReleaseEmptyManifestCompilationProfile
      | Set.null (releaseProfileRequiredTrustKinds profile) =
          Left CertifiedReleaseEmptyRequiredTrustDomain
      | otherwise = Right ()

    validateManifestProfile
      | manifestTarget manifest /= releaseProfileManifestTarget profile =
          Left (CertifiedReleaseManifestTargetMismatch
            (releaseProfileManifestTarget profile)
            (manifestTarget manifest))
      | manifestCompilationProfile manifest
          /= releaseProfileManifestCompilationProfile profile =
          Left (CertifiedReleaseManifestCompilationProfileMismatch
            (releaseProfileManifestCompilationProfile profile)
            (manifestCompilationProfile manifest))
      | otherwise = Right ()

    systemsArtifact =
      phase1StageSystemsArtifact
        . subjectStageBase
        . concreteSubjectStage
        . stageClosureConcrete
        $ stage

    expectedSystemsDigest = systemsArtifactDigest systemsArtifact
    expectedLoweringRoot =
      loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)

    validateSystemsBinding
      | manifestImplementationDigest manifest /= expectedSystemsDigest =
          Left (CertifiedReleaseManifestImplementationDigestMismatch
            expectedSystemsDigest
            (manifestImplementationDigest manifest))
      | manifestLoweringLedgerRoot manifest /= expectedLoweringRoot =
          Left (CertifiedReleaseManifestLoweringLedgerRootMismatch
            expectedLoweringRoot
            (manifestLoweringLedgerRoot manifest))
      | otherwise = Right ()

    llvmModule = llvmArtifactModule artifact
    llvmContract = llvmArtifactContract artifact
    actualTarget = targetProfileFromModule llvmModule
    expectedTarget = releaseProfileLLVMTarget profile
    expectedTargetDigest = llvmModuleDigest llvmModule

    validateLLVM
      | llvmContractSourceDigest llvmContract /= expectedSystemsDigest =
          Left (CertifiedReleaseLLVMSourceDigestMismatch
            expectedSystemsDigest
            (llvmContractSourceDigest llvmContract))
      | llvmContractTargetDigest llvmContract /= expectedTargetDigest =
          Left (CertifiedReleaseLLVMTargetDigestMismatch
            expectedTargetDigest
            (llvmContractTargetDigest llvmContract))
      | llvmArtifactText artifact /= renderLLVMModule llvmModule =
          Left CertifiedReleaseLLVMTextMismatch
      | actualTarget /= expectedTarget =
          Left (CertifiedReleaseLLVMTargetProfileMismatch expectedTarget actualTarget)
      | otherwise = Right ()

    validateTrustBoundaries values = do
      mapM_ validateTrustBoundary values
      let pairs = [(releaseTrustBoundaryId value, value) | value <- values]
          boundaries = Map.fromList pairs
      case firstDuplicate (map fst pairs) of
        Just duplicateId -> Left (CertifiedReleaseDuplicateTrustBoundary duplicateId)
        Nothing -> Right ()
      let actualKinds = Set.fromList (map releaseTrustKind values)
          expectedKinds = releaseProfileRequiredTrustKinds profile
      if actualKinds == expectedKinds
        then Right boundaries
        else Left (CertifiedReleaseTrustKindDomainMismatch expectedKinds actualKinds)

    validateTrustBoundary boundary
      | blank (unReleaseTrustBoundaryId (releaseTrustBoundaryId boundary)) =
          Left CertifiedReleaseEmptyTrustBoundaryId
      | blank (releaseTrustName boundary) =
          Left (CertifiedReleaseEmptyTrustName (releaseTrustBoundaryId boundary))
      | blank (releaseTrustRevision boundary) =
          Left (CertifiedReleaseEmptyTrustRevision (releaseTrustBoundaryId boundary))
      | blank (releaseTrustBasis boundary) =
          Left (CertifiedReleaseEmptyTrustBasis (releaseTrustBoundaryId boundary))
      | otherwise = Right ()

blank :: Text -> Bool
blank = Text.null . Text.strip

targetProfileFromModule :: LLVMModule -> LLVMTargetProfile
targetProfileFromModule moduleValue = LLVMTargetProfile
  { llvmTargetLanguageVersion = llvmLanguageVersion moduleValue
  , llvmTargetToolVersion = llvmToolVersion moduleValue
  , llvmTargetTripleName = llvmTargetTriple moduleValue
  , llvmTargetDataLayout = llvmDataLayout moduleValue
  , llvmTargetRuntimeABIDigest = llvmRuntimeABIDigest moduleValue
  , llvmTargetRuntimeABIProfile = llvmRuntimeABIProfile moduleValue
  }

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (value : rest)
      | Set.member value seen = Just value
      | otherwise = go (Set.insert value seen) rest

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
