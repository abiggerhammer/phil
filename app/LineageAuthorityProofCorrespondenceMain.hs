{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Assurance.Verify
import Phil.Core.Syntax (ObligationId (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "explicit in-scope obligation dependency verifies" explicitDependencyVerifies
    , test "generated prerequisite may justify its parent without false cycle" generatedPrerequisiteDependencyPasses
    , test "genuine two-way obligation justification cycle rejects" genuineObligationCycleRejects
    , test "lineage plus ancestor evidence does not authorize child" lineageWithoutChildEvidenceRejects
    , test "lineage parent must remain present in manifest" missingLineageParentRejects
    , test "exported historical ancestor may remain lineage" exportedHistoricalAncestorPasses
    , test "exported historical ancestor cannot be justification dependency" exportedAncestorDependencyRejects
    , test "explicit justification dependency does not require lineage" dependencyWithoutLineagePasses
    ]
  if and results then pure () else exitFailure

explicitDependencyVerifies :: Bool
explicitDependencyVerifies =
  let (ledger, manifest, context, _) = fixture True True True
  in verifyManifest context ledger manifest == Right ()

generatedPrerequisiteDependencyPasses :: Bool
generatedPrerequisiteDependencyPasses =
  let (ledger0, manifest0, context, ids) = fixture True False True
      ledger = adjustEvidence (parentEvidenceId ids)
        (\entry -> entry
          { evidenceDependsOn = [DependsOnObligation (childRevisionId ids)] })
        ledger0
      manifest = seal ledger manifest0
  in verifyManifest context ledger manifest == Right ()

genuineObligationCycleRejects :: Bool
genuineObligationCycleRejects =
  let (ledger0, manifest0, context, ids) = fixture True True True
      ledger = adjustEvidence (parentEvidenceId ids)
        (\entry -> entry
          { evidenceDependsOn = [DependsOnObligation (childRevisionId ids)] })
        ledger0
      manifest = seal ledger manifest0
  in case verifyManifest context ledger manifest of
      Left (JustificationCycle _) -> True
      _ -> False

lineageWithoutChildEvidenceRejects :: Bool
lineageWithoutChildEvidenceRejects =
  let (ledger0, manifest0, context, ids) = fixture True False True
      ledger = ledger0
      manifest = seal ledger manifest0
        { manifestEvidenceEntries = Set.singleton (parentEvidenceId ids) }
  in case verifyManifest context ledger manifest of
      Left (AcceptanceRuleUnsatisfied revision) -> revision == childRevisionId ids
      _ -> False

missingLineageParentRejects :: Bool
missingLineageParentRejects =
  let (ledger0, manifest0, context0, ids) = fixture True True False
      ledger = ledger0
      child = childRevisionId ids
      manifest = seal ledger manifest0
        { manifestObligationRevisions = Set.singleton child
        , manifestCertificationScope = Set.singleton child
        , manifestEvidenceEntries = Set.singleton (childEvidenceId ids)
        }
      context = context0
        { verificationExpectedObligations = Set.singleton child }
  in case verifyManifest context ledger manifest of
      Left (MissingObligationDependency marker parent) ->
        marker == EvidenceEntryId "<revision-lineage>"
          && parent == parentRevisionId ids
      _ -> False

exportedHistoricalAncestorPasses :: Bool
exportedHistoricalAncestorPasses =
  let (ledger0, manifest0, context0, ids) = fixture True False True
      export = mkExport (parentRevisionId ids)
      childEvidence = independentChildEvidence ledger0 ids
      ledger = ledger0
        { ledgerEvidence = Map.insert
            (evidenceEntryId childEvidence)
            childEvidence
            (ledgerEvidence ledger0)
        , ledgerExports = Map.singleton (exportId export) export
        }
      manifest = seal ledger manifest0
        { manifestCertificationScope = Set.singleton (childRevisionId ids)
        , manifestEvidenceEntries = Set.singleton (evidenceEntryId childEvidence)
        , manifestExports = Set.singleton (exportId export)
        }
      context = context0
        { verificationPermittedExportBoundaries = Set.singleton "history.archive" }
  in verifyManifest context ledger manifest == Right ()

exportedAncestorDependencyRejects :: Bool
exportedAncestorDependencyRejects =
  let (ledger0, manifest0, context0, ids) = fixture True True True
      export = mkExport (parentRevisionId ids)
      ledger = ledger0 { ledgerExports = Map.singleton (exportId export) export }
      manifest = seal ledger manifest0
        { manifestCertificationScope = Set.singleton (childRevisionId ids)
        , manifestEvidenceEntries = Set.singleton (childEvidenceId ids)
        , manifestExports = Set.singleton (exportId export)
        }
      context = context0
        { verificationPermittedExportBoundaries = Set.singleton "history.archive" }
  in case verifyManifest context ledger manifest of
      Left (DependencyOnExportedObligation owner parent) ->
        owner == childEvidenceId ids && parent == parentRevisionId ids
      _ -> False

dependencyWithoutLineagePasses :: Bool
dependencyWithoutLineagePasses =
  let (ledger, manifest, context, _) = fixture False True True
  in verifyManifest context ledger manifest == Right ()

data FixtureIds = FixtureIds
  { parentRevisionId :: RevisionId
  , childRevisionId :: RevisionId
  , parentEvidenceId :: EvidenceEntryId
  , childEvidenceId :: EvidenceEntryId
  }

fixture
  :: Bool
  -> Bool
  -> Bool
  -> (AssuranceLedger, AssuranceManifest, VerificationContext, FixtureIds)
fixture includeLineage childDependsOnParent selectParentEvidence =
  (ledger, manifest, context, ids)
  where
    parent = mkRevision
      "test.lineage.parent"
      "historical parent statement"
      []
    parents = if includeLineage then [revisionId parent] else []
    child = mkRevision
      "test.lineage.child"
      "current child statement"
      parents
    parentEvidence = mkEvidence
      "evidence.test.lineage.parent"
      parent
      []
    childDependencies =
      if childDependsOnParent
        then [DependsOnObligation (revisionId parent)]
        else []
    childEvidence = mkEvidence
      "evidence.test.lineage.child"
      child
      childDependencies
    selectedEvidence =
      (if selectParentEvidence then [parentEvidence] else []) <> [childEvidence]
    ledger = emptyLedger
      { ledgerRevisions = Map.fromList
          [ (revisionId parent, parent)
          , (revisionId child, child)
          ]
      , ledgerEvidence = Map.fromList
          [ (evidenceEntryId parentEvidence, parentEvidence)
          , (evidenceEntryId childEvidence, childEvidence)
          ]
      }
    revisionSet = Set.fromList [revisionId parent, revisionId child]
    provisionalManifest = emptyManifest
      { manifestArchitectureDigest = digestText "lineage-authority architecture"
      , manifestPhilCoreDigest = digestText "lineage-authority core"
      , manifestImplementationDigest = digestText "lineage-authority implementation"
      , manifestTarget = "assurance-lineage"
      , manifestCompilationProfile = "proof-correspondence"
      , manifestObligationRevisions = revisionSet
      , manifestCertificationScope = revisionSet
      , manifestEvidenceEntries = Set.fromList (map evidenceEntryId selectedEvidence)
      , manifestLoweringLedgerRoot = digestText "lineage-authority lowering root"
      }
    manifest = seal ledger provisionalManifest
    context = emptyVerificationContext
      { verificationArchitectureDigest = manifestArchitectureDigest manifest
      , verificationPhilCoreDigest = manifestPhilCoreDigest manifest
      , verificationImplementationDigest = manifestImplementationDigest manifest
      , verificationTarget = manifestTarget manifest
      , verificationCompilationProfile = manifestCompilationProfile manifest
      , verificationExpectedObligations = manifestObligationRevisions manifest
      , verificationLoweringLedgerRoot = manifestLoweringLedgerRoot manifest
      }
    ids = FixtureIds
      { parentRevisionId = revisionId parent
      , childRevisionId = revisionId child
      , parentEvidenceId = evidenceEntryId parentEvidence
      , childEvidenceId = evidenceEntryId childEvidence
      }

mkRevision :: Text -> Text -> [RevisionId] -> ObligationRevision
mkRevision stable statement parents = provisional
  { revisionId = deriveRevisionId provisional }
  where
    provisional = ObligationRevision
      { revisionObligationId = ObligationId stable
      , revisionId = RevisionId ""
      , revisionStatement = statement
      , revisionStatementDigest = digestText statement
      , revisionKind = "LineageAuthorityTest"
      , revisionOrigin = "app/LineageAuthorityProofCorrespondenceMain.hs"
      , revisionScope = "test.assurance.lineage"
      , revisionRequiredAt = "certification"
      , revisionRepresentation = "minimal lineage/authority fixture"
      , revisionSubjectIds = []
      , revisionContextIds = []
      , revisionAcceptanceRule = AcceptEntry KernelChecked (EvidenceRole "establishes")
      , revisionGeneratedFrom = parents
      }

mkEvidence :: Text -> ObligationRevision -> [EvidenceDependency] -> EvidenceEntry
mkEvidence stable revision dependencies = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId stable
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = KernelChecked
      , evidenceRole = EvidenceRole "establishes"
      , evidenceProducer = "lineage-authority correspondence fixture"
      , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = dependencies
      , evidenceValidityScope = ValidityScope Map.empty
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = ["lineage/authority correspondence"]
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

independentChildEvidence :: AssuranceLedger -> FixtureIds -> EvidenceEntry
independentChildEvidence ledger ids =
  case Map.lookup (childRevisionId ids) (ledgerRevisions ledger) of
    Nothing -> error "lineage fixture lost child revision"
    Just child -> mkEvidence
      "evidence.test.lineage.child.independent"
      child
      []

mkExport :: RevisionId -> ExportEntry
mkExport revision = provisional
  { exportDigest = deriveExportDigest provisional }
  where
    provisional = ExportEntry
      { exportId = ExportId "export.test.lineage.parent"
      , exportDigest = Digest ""
      , exportObligationRevision = revision
      , exportDestinationBoundary = "history.archive"
      , exportDerivedObligationId = ObligationId "test.lineage.parent.exported"
      , exportValidityScope = ValidityScope Map.empty
      }

seal :: AssuranceLedger -> AssuranceManifest -> AssuranceManifest
seal ledger manifest = manifest { manifestId = deriveManifestId ledger manifest }

adjustEvidence
  :: EvidenceEntryId
  -> (EvidenceEntry -> EvidenceEntry)
  -> AssuranceLedger
  -> AssuranceLedger
adjustEvidence key modify ledger = ledger
  { ledgerEvidence = Map.adjust update key (ledgerEvidence ledger) }
  where
    update entry =
      let changed = modify entry
      in changed { evidenceEntryDigest = deriveEvidenceEntryDigest changed }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
