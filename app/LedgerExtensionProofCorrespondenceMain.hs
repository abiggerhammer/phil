{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Assurance.Verify
import Phil.Core.Syntax (ObligationId (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "ledger extension is reflexive" reflexivePasses
    , test "first adjacent ledger extension verifies" firstStepPasses
    , test "second adjacent ledger extension verifies" secondStepPasses
    , test "two-step ledger extension collapses root to tip" collapsedStepPasses
    , test "revision rewrite is rejected" revisionRewriteRejects
    , test "evidence rewrite is rejected" evidenceRewriteRejects
    , test "assumption rewrite is rejected" assumptionRewriteRejects
    , test "export rewrite is rejected" exportRewriteRejects
    , test "assurance-use rewrite is rejected" useRewriteRejects
    , test "root-to-tip check can miss lost intermediate addition" rootToTipCanMissIntermediateLoss
    , test "adjacent check catches lost intermediate addition" adjacentCheckCatchesIntermediateLoss
    ]
  if and results then pure () else exitFailure

reflexivePasses :: Bool
reflexivePasses = verifyLedgerExtension ledgerA ledgerA == Right ()

firstStepPasses :: Bool
firstStepPasses = verifyLedgerExtension ledgerA ledgerB == Right ()

secondStepPasses :: Bool
secondStepPasses = verifyLedgerExtension ledgerB ledgerC == Right ()

collapsedStepPasses :: Bool
collapsedStepPasses = verifyLedgerExtension ledgerA ledgerC == Right ()

revisionRewriteRejects :: Bool
revisionRewriteRejects =
  rejectsMutation "obligation revision" ledgerA (mutateRevision ledgerC revisionAId)

evidenceRewriteRejects :: Bool
evidenceRewriteRejects =
  rejectsMutation "evidence entry" ledgerA (mutateEvidence ledgerC evidenceAId)

assumptionRewriteRejects :: Bool
assumptionRewriteRejects =
  rejectsMutation "assumption" ledgerA (mutateAssumption ledgerC assumptionAId)

exportRewriteRejects :: Bool
exportRewriteRejects =
  rejectsMutation "export" ledgerA (mutateExport ledgerC exportAId)

useRewriteRejects :: Bool
useRewriteRejects =
  rejectsMutation "assurance use" ledgerA (mutateUse ledgerC useAId)

rootToTipCanMissIntermediateLoss :: Bool
rootToTipCanMissIntermediateLoss =
  verifyLedgerExtension ledgerA ledgerCLosesIntermediate == Right ()

adjacentCheckCatchesIntermediateLoss :: Bool
adjacentCheckCatchesIntermediateLoss =
  case verifyLedgerExtension ledgerB ledgerCLosesIntermediate of
    Left (LedgerHistoryMutation "assumption") -> True
    _ -> False

rejectsMutation :: Text -> AssuranceLedger -> AssuranceLedger -> Bool
rejectsMutation label before after =
  case verifyLedgerExtension before after of
    Left (LedgerHistoryMutation actual) -> actual == label
    _ -> False

ledgerA :: AssuranceLedger
ledgerA = ledgerOf revisionA evidenceA assumptionA exportA useA

ledgerB :: AssuranceLedger
ledgerB = appendGeneration ledgerA revisionB evidenceB assumptionB exportB useB

ledgerC :: AssuranceLedger
ledgerC = appendGeneration ledgerB revisionC evidenceC assumptionC exportC useC

ledgerCLosesIntermediate :: AssuranceLedger
ledgerCLosesIntermediate = ledgerC
  { ledgerAssumptions = Map.delete assumptionBId (ledgerAssumptions ledgerC) }

appendGeneration
  :: AssuranceLedger
  -> ObligationRevision
  -> EvidenceEntry
  -> Assumption
  -> ExportEntry
  -> AssuranceUse
  -> AssuranceLedger
appendGeneration ledger revision evidence assumption exportEntry assuranceUse = ledger
  { ledgerRevisions = Map.insert (revisionId revision) revision (ledgerRevisions ledger)
  , ledgerEvidence = Map.insert (evidenceEntryId evidence) evidence (ledgerEvidence ledger)
  , ledgerAssumptions = Map.insert (assumptionId assumption) assumption (ledgerAssumptions ledger)
  , ledgerExports = Map.insert (exportId exportEntry) exportEntry (ledgerExports ledger)
  , ledgerUses = Map.insert (assuranceUseId assuranceUse) assuranceUse (ledgerUses ledger)
  }

ledgerOf
  :: ObligationRevision
  -> EvidenceEntry
  -> Assumption
  -> ExportEntry
  -> AssuranceUse
  -> AssuranceLedger
ledgerOf revision evidence assumption exportEntry assuranceUse = emptyLedger
  { ledgerRevisions = Map.singleton (revisionId revision) revision
  , ledgerEvidence = Map.singleton (evidenceEntryId evidence) evidence
  , ledgerAssumptions = Map.singleton (assumptionId assumption) assumption
  , ledgerExports = Map.singleton (exportId exportEntry) exportEntry
  , ledgerUses = Map.singleton (assuranceUseId assuranceUse) assuranceUse
  }

revisionA, revisionB, revisionC :: ObligationRevision
revisionA = mkRevision "a" "ledger generation A"
revisionB = mkRevision "b" "ledger generation B"
revisionC = mkRevision "c" "ledger generation C"

revisionAId :: RevisionId
revisionAId = revisionId revisionA

mkRevision :: Text -> Text -> ObligationRevision
mkRevision suffix statement = provisional
  { revisionId = deriveRevisionId provisional }
  where
    provisional = ObligationRevision
      { revisionObligationId = ObligationId ("test.ledger." <> suffix)
      , revisionId = RevisionId ""
      , revisionStatement = statement
      , revisionStatementDigest = digestText statement
      , revisionKind = "LedgerExtensionTest"
      , revisionOrigin = "app/LedgerExtensionProofCorrespondenceMain.hs"
      , revisionScope = "test.assurance.ledger-extension"
      , revisionRequiredAt = "certification"
      , revisionRepresentation = "minimal append-only ledger fixture"
      , revisionSubjectIds = []
      , revisionContextIds = []
      , revisionAcceptanceRule = AcceptEntry KernelChecked (EvidenceRole "establishes")
      , revisionGeneratedFrom = []
      }

evidenceA, evidenceB, evidenceC :: EvidenceEntry
evidenceA = mkEvidence "a" revisionA
evidenceB = mkEvidence "b" revisionB
evidenceC = mkEvidence "c" revisionC

evidenceAId :: EvidenceEntryId
evidenceAId = evidenceEntryId evidenceA

mkEvidence :: Text -> ObligationRevision -> EvidenceEntry
mkEvidence suffix revision = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId ("evidence.test.ledger." <> suffix)
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = KernelChecked
      , evidenceRole = EvidenceRole "establishes"
      , evidenceProducer = "ledger-extension correspondence fixture"
      , evidenceChecker = "Phil.Assurance.Verify.verifyLedgerExtension"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = ValidityScope Map.empty
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = ["append-only ledger correspondence"]
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

assumptionA, assumptionB, assumptionC :: Assumption
assumptionA = mkAssumption "a" "assumption A"
assumptionB = mkAssumption "b" "assumption B"
assumptionC = mkAssumption "c" "assumption C"

assumptionAId, assumptionBId :: AssumptionId
assumptionAId = assumptionId assumptionA
assumptionBId = assumptionId assumptionB

mkAssumption :: Text -> Text -> Assumption
mkAssumption suffix statement = provisional
  { assumptionDigest = deriveAssumptionDigest provisional }
  where
    provisional = Assumption
      { assumptionId = AssumptionId ("assumption.test.ledger." <> suffix)
      , assumptionDigest = Digest ""
      , assumptionStatement = statement
      , assumptionScope = "test.assurance.ledger-extension"
      , assumptionOwnerBoundary = "test"
      , assumptionRationale = "ledger-extension correspondence fixture"
      , assumptionValidityScope = ValidityScope Map.empty
      }

exportA, exportB, exportC :: ExportEntry
exportA = mkExport "a" revisionA
exportB = mkExport "b" revisionB
exportC = mkExport "c" revisionC

exportAId :: ExportId
exportAId = exportId exportA

mkExport :: Text -> ObligationRevision -> ExportEntry
mkExport suffix revision = provisional
  { exportDigest = deriveExportDigest provisional }
  where
    provisional = ExportEntry
      { exportId = ExportId ("export.test.ledger." <> suffix)
      , exportDigest = Digest ""
      , exportObligationRevision = revisionId revision
      , exportDestinationBoundary = "history.archive"
      , exportDerivedObligationId = ObligationId ("test.ledger.export." <> suffix)
      , exportValidityScope = ValidityScope Map.empty
      }

useA, useB, useC :: AssuranceUse
useA = mkUse "a" revisionA evidenceA
useB = mkUse "b" revisionB evidenceB
useC = mkUse "c" revisionC evidenceC

useAId :: AssuranceUseId
useAId = assuranceUseId useA

mkUse :: Text -> ObligationRevision -> EvidenceEntry -> AssuranceUse
mkUse suffix revision evidence = sealed
  where
    provisional = ErasureUse
      { assuranceUseId = AssuranceUseId ("use.test.ledger." <> suffix)
      , assuranceUseDigest = Digest ""
      , useObligationRevision = revisionId revision
      , useEvidenceEntries = [evidenceEntryId evidence]
      }
    sealed = provisional
      { assuranceUseDigest = deriveAssuranceUseDigest provisional }

mutateRevision :: AssuranceLedger -> RevisionId -> AssuranceLedger
mutateRevision ledger key = ledger
  { ledgerRevisions = Map.adjust
      (\revision -> revision { revisionStatement = "rewritten revision" })
      key
      (ledgerRevisions ledger)
  }

mutateEvidence :: AssuranceLedger -> EvidenceEntryId -> AssuranceLedger
mutateEvidence ledger key = ledger
  { ledgerEvidence = Map.adjust
      (\entry -> entry { evidenceProducer = "rewritten producer" })
      key
      (ledgerEvidence ledger)
  }

mutateAssumption :: AssuranceLedger -> AssumptionId -> AssuranceLedger
mutateAssumption ledger key = ledger
  { ledgerAssumptions = Map.adjust
      (\assumption -> assumption { assumptionStatement = "rewritten assumption" })
      key
      (ledgerAssumptions ledger)
  }

mutateExport :: AssuranceLedger -> ExportId -> AssuranceLedger
mutateExport ledger key = ledger
  { ledgerExports = Map.adjust
      (\exportEntry -> exportEntry { exportDestinationBoundary = "rewritten.boundary" })
      key
      (ledgerExports ledger)
  }

mutateUse :: AssuranceLedger -> AssuranceUseId -> AssuranceLedger
mutateUse ledger key = ledger
  { ledgerUses = Map.adjust
      (\assuranceUse -> assuranceUse { assuranceUseDigest = digestText "rewritten use" })
      key
      (ledgerUses ledger)
  }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
