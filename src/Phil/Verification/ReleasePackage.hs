{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.ReleasePackage
  ( ReleasePackageRevision (..)
  , certifiedReleasePackageRevisionV1
  , CertifiedReleasePackage
  , certifiedReleasePackageId
  , certifiedReleasePackageManifestId
  , certifiedReleasePackageLoweringLedgerRoot
  , certifiedReleasePackageLLVMTargetDigest
  , certifiedReleasePackageCostRefs
  , certifiedReleasePackageTrustBoundaryIds
  , certifiedReleasePackageLoweringDecisionCount
  , ReleasePackageError (..)
  , buildCertifiedReleasePackage
  , renderCertifiedReleasePackage
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( AssuranceLedger (..)
  , AssuranceManifest (..)
  , AssuranceUse (..)
  , AssuranceUseId (..)
  , AssumptionId (..)
  , Digest (..)
  , EvidenceEntry (..)
  , EvidenceEntryId (..)
  , ExportId (..)
  , RevisionId (..)
  , deriveManifestId
  , digestText
  )
import Phil.LLVM.IR
  ( LLVMArtifact (..)
  , LLVMEmissionContract (..)
  , LLVMModule (..)
  , llvmModuleDigest
  )
import Phil.Systems.IR
  ( CostShape (..)
  , DecisionId (..)
  , LoweringDecision (..)
  , LoweringLedger (..)
  , SystemsArtifact (..)
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , concreteSubjectStage
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )
import Phil.Verification.CertifiedRelease
  ( CertifiedReleaseArtifact
  , CertifiedReleaseProfile (..)
  , ReleaseProfileRevision (..)
  , ReleaseTrustBoundary (..)
  , ReleaseTrustBoundaryId (..)
  , certifiedReleaseLLVMArtifact
  , certifiedReleaseManifest
  , certifiedReleaseProfile
  , certifiedReleaseStageClosure
  , certifiedReleaseTrustBoundaries
  )

newtype ReleasePackageRevision = ReleasePackageRevision
  { unReleasePackageRevision :: Text
  }
  deriving (Eq, Ord, Show)

certifiedReleasePackageRevisionV1 :: ReleasePackageRevision
certifiedReleasePackageRevisionV1 =
  ReleasePackageRevision "phase1.int005.certified-release-package.v1"

-- | Canonical, inspectable metadata sidecar for one already-certified release.
-- The exact LLVM text remains a separate release artifact; this package binds
-- its digest to the final assurance manifest, lowering/cost lineage, and the
-- explicitly named residual TCB.
data CertifiedReleasePackage = CertifiedReleasePackage
  { certifiedReleasePackageId :: Digest
  , certifiedReleasePackageManifestId :: Digest
  , certifiedReleasePackageLoweringLedgerRoot :: Digest
  , certifiedReleasePackageLLVMTargetDigest :: Digest
  , certifiedReleasePackageCostRefs :: Set Text
  , certifiedReleasePackageTrustBoundaryIds :: Set ReleaseTrustBoundaryId
  , certifiedReleasePackageLoweringDecisionCount :: Int
  , certifiedReleasePackageBody :: Text
  }
  deriving (Eq, Show)

data ReleasePackageError
  = ReleasePackageManifestLedgerMismatch Digest Digest
  | ReleasePackageMissingEvidence EvidenceEntryId
  | ReleasePackageMissingAssuranceUse AssuranceUseId
  deriving (Eq, Show)

buildCertifiedReleasePackage
  :: AssuranceLedger
  -> CertifiedReleaseArtifact
  -> Either ReleasePackageError CertifiedReleasePackage
buildCertifiedReleasePackage ledger release = do
  let manifest = certifiedReleaseManifest release
      expectedManifestId = manifestId manifest
      actualManifestId = deriveManifestId ledger manifest
  if actualManifestId == expectedManifestId
    then pure ()
    else Left (ReleasePackageManifestLedgerMismatch expectedManifestId actualManifestId)

  selectedEvidence <- mapM lookupEvidence
    (Set.toAscList (manifestEvidenceEntries manifest))
  selectedUses <- mapM lookupUse
    (Set.toAscList (manifestAssuranceUses manifest))

  let stage = certifiedReleaseStageClosure release
      systems = stageSystemsArtifact stage
      loweringLedger = systemsArtifactLoweringLedger systems
      decisions = loweringLedgerDecisions loweringLedger
      llvm = certifiedReleaseLLVMArtifact release
      llvmContract = llvmArtifactContract llvm
      body = renderBody release selectedEvidence selectedUses decisions
      packageId = digestText body
      evidenceCosts = Set.fromList
        [ costRef
        | (_, entry) <- selectedEvidence
        , costRef <- evidenceCostRefs entry
        ]
      useCosts = Set.fromList
        [ useCostRef use
        | (_, use@RetainedRuntimeUse {}) <- selectedUses
        ]
      costs = Set.union evidenceCosts useCosts
  pure CertifiedReleasePackage
    { certifiedReleasePackageId = packageId
    , certifiedReleasePackageManifestId = expectedManifestId
    , certifiedReleasePackageLoweringLedgerRoot = loweringLedgerRoot loweringLedger
    , certifiedReleasePackageLLVMTargetDigest = llvmContractTargetDigest llvmContract
    , certifiedReleasePackageCostRefs = costs
    , certifiedReleasePackageTrustBoundaryIds =
        Map.keysSet (certifiedReleaseTrustBoundaries release)
    , certifiedReleasePackageLoweringDecisionCount = Map.size decisions
    , certifiedReleasePackageBody = body
    }
  where
    lookupEvidence key = case Map.lookup key (ledgerEvidence ledger) of
      Nothing -> Left (ReleasePackageMissingEvidence key)
      Just entry -> Right (key, entry)

    lookupUse key = case Map.lookup key (ledgerUses ledger) of
      Nothing -> Left (ReleasePackageMissingAssuranceUse key)
      Just use -> Right (key, use)

renderCertifiedReleasePackage :: CertifiedReleasePackage -> Text
renderCertifiedReleasePackage package = Text.unlines
  [ recordLine "package" [("id", unDigest (certifiedReleasePackageId package))]
  , certifiedReleasePackageBody package
  ]

renderBody
  :: CertifiedReleaseArtifact
  -> [(EvidenceEntryId, EvidenceEntry)]
  -> [(AssuranceUseId, AssuranceUse)]
  -> Map.Map DecisionId LoweringDecision
  -> Text
renderBody release selectedEvidence selectedUses decisions = Text.unlines $
  [ recordLine "format"
      [("revision", unReleasePackageRevision certifiedReleasePackageRevisionV1)]
  , recordLine "release-profile"
      [("revision", unReleaseProfileRevision (releaseProfileRevision profile))]
  , recordLine "manifest"
      [ ("id", unDigest (manifestId manifest))
      , ("architecture", unDigest (manifestArchitectureDigest manifest))
      , ("core", unDigest (manifestPhilCoreDigest manifest))
      , ("implementation", unDigest (manifestImplementationDigest manifest))
      , ("target", manifestTarget manifest)
      , ("compilation-profile", manifestCompilationProfile manifest)
      , ("lowering-ledger-root", unDigest (manifestLoweringLedgerRoot manifest))
      ]
  , recordLine "llvm"
      [ ("source-digest", unDigest (llvmContractSourceDigest llvmContract))
      , ("target-digest", unDigest (llvmContractTargetDigest llvmContract))
      , ("module-digest", unDigest (llvmModuleDigest llvmModule))
      , ("language", llvmLanguageVersion llvmModule)
      , ("tool", llvmToolVersion llvmModule)
      , ("target-triple", llvmTargetTriple llvmModule)
      , ("data-layout", llvmDataLayout llvmModule)
      , ("runtime-abi-digest", unDigest (llvmRuntimeABIDigest llvmModule))
      , ("runtime-abi-profile", llvmRuntimeABIProfile llvmModule)
      ]
  ]
  <> map (recordOne "obligation" "id" . unRevisionId)
      (Set.toAscList (manifestObligationRevisions manifest))
  <> map (recordOne "certification-scope" "id" . unRevisionId)
      (Set.toAscList (manifestCertificationScope manifest))
  <> map (recordOne "assumption" "id" . unAssumptionId)
      (Set.toAscList (manifestAssumptionNodes manifest))
  <> map (recordOne "export" "id" . unExportId)
      (Set.toAscList (manifestExports manifest))
  <> concatMap renderEvidence selectedEvidence
  <> concatMap renderUse selectedUses
  <> map renderDecision (Map.toAscList decisions)
  <> map renderTrust (Map.toAscList (certifiedReleaseTrustBoundaries release))
  where
    manifest = certifiedReleaseManifest release
    profile = certifiedReleaseProfile release
    llvm = certifiedReleaseLLVMArtifact release
    llvmModule = llvmArtifactModule llvm
    llvmContract = llvmArtifactContract llvm

    renderEvidence (key, entry) =
      [ recordLine "evidence"
          [ ("id", unEvidenceEntryId key)
          , ("digest", unDigest (evidenceEntryDigest entry))
          ]
      ] <> [ recordLine "evidence-cost"
              [ ("evidence", unEvidenceEntryId key)
              , ("cost-ref", costRef)
              ]
           | costRef <- evidenceCostRefs entry
           ]

    renderUse (key, use) = case use of
      ErasureUse
        { assuranceUseDigest = useDigest
        , useObligationRevision = revision
        , useEvidenceEntries = entries
        } ->
          [ recordLine "assurance-use"
              [ ("id", unAssuranceUseId key)
              , ("digest", unDigest useDigest)
              , ("kind", "erasure")
              , ("revision", unRevisionId revision)
              ]
          ] <> [ recordLine "assurance-use-evidence"
                  [ ("use", unAssuranceUseId key)
                  , ("evidence", unEvidenceEntryId entry)
                  ]
               | entry <- entries
               ]
      RetainedRuntimeUse
        { assuranceUseDigest = useDigest
        , useObligationRevision = revision
        , useRuntimeEvidence = entry
        , useCostRef = costRef
        } ->
          [ recordLine "assurance-use"
              [ ("id", unAssuranceUseId key)
              , ("digest", unDigest useDigest)
              , ("kind", "retained-runtime")
              , ("revision", unRevisionId revision)
              , ("evidence", unEvidenceEntryId entry)
              , ("cost-ref", costRef)
              ]
          ]

    renderDecision (key, decision) = recordLine "lowering-decision"
      [ ("id", unDecisionId key)
      , ("digest", unDigest (loweringDecisionDigest decision))
      , ("source", unDigest (loweringSourceArtifactDigest decision))
      , ("target", unDigest (loweringTargetArtifactDigest decision))
      , ("action", Text.pack (show (loweringAction decision)))
      , ("cost-class", maybe "none" (Text.pack . show) (loweringCostClass decision))
      , ("cost-shape", renderCostShape (loweringCostShape decision))
      ]

    renderTrust (key, boundary) = recordLine "tcb"
      [ ("id", unReleaseTrustBoundaryId key)
      , ("kind", Text.pack (show (releaseTrustKind boundary)))
      , ("name", releaseTrustName boundary)
      , ("revision", releaseTrustRevision boundary)
      , ("basis", releaseTrustBasis boundary)
      ]

stageSystemsArtifact :: StageClosureBundle -> SystemsArtifact
stageSystemsArtifact = phase1StageSystemsArtifact
  . subjectStageBase
  . concreteSubjectStage
  . stageClosureConcrete

renderCostShape :: CostShape -> Text
renderCostShape cost = Text.intercalate ";"
  [ costField "compile-time" (costCompileTime cost)
  , costField "code-size" (costCodeSize cost)
  , costField "allocation-count" (costAllocationCount cost)
  , costField "peak-live-memory" (costPeakLiveMemory cost)
  , costField "bytes-copied" (costBytesCopied cost)
  , costField "dynamic-check-count" (costDynamicCheckCount cost)
  , costField "branch-or-dispatch" (costBranchOrDispatch cost)
  , costField "hash-or-crypto-work" (costHashOrCryptoWork cost)
  , costField "synchronization" (costSynchronization cost)
  , costField "frequency" (costFrequency cost)
  ]
  where
    costField name value = name <> "=" <> maybe "none" escapeText value

recordOne :: Text -> Text -> Text -> Text
recordOne tag key value = recordLine tag [(key, value)]

recordLine :: Text -> [(Text, Text)] -> Text
recordLine tag fields = Text.intercalate "\t"
  (tag : [key <> "=" <> escapeText value | (key, value) <- fields])

escapeText :: Text -> Text
escapeText = Text.concatMap escapeChar
  where
    escapeChar '\\' = "\\\\"
    escapeChar '\n' = "\\n"
    escapeChar '\r' = "\\r"
    escapeChar '\t' = "\\t"
    escapeChar char = Text.singleton char
