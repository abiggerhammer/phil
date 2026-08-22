{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Phase 0 upload reference manifest verifies" referenceManifestVerifies
    , test "Core obligation handoff is stable for unchanged semantics" coreRevisionStable
    , test "changed Core propositions get new revision identities" changedCoreClaimChangesRevision
    , test "tampered revision statement digest rejects" tamperedRevisionRejects
    , test "missing required runtime evidence leaves obligation unresolved" missingRuntimeEvidenceRejects
    , test "unpermitted assumptions reject" unpermittedAssumptionRejects
    , test "stale validity scope rejects" staleValidityScopeRejects
    , test "unknown ADR-011 cost references reject" missingCostReferenceRejects
    , test "selected rejected evidence cannot certify" rejectedEvidenceRejects
    , test "empty acceptance rules cannot certify vacuously" emptyAcceptanceRuleRejects
    , test "mutual evidence dependencies are detected as cycles" evidenceCycleRejects
    , test "artifact-requiring assurance cannot omit its artifact" requiredArtifactRejects
    , test "artifact digests are checked against trusted availability" artifactDigestMismatchRejects
    , test "out-of-scope obligations require an explicit export" missingExportRejects
    , test "permitted export closes only the bounded local scope" permittedExportPasses
    , test "unpermitted export boundaries reject" unpermittedExportRejects
    , test "evidence cannot depend on an exported obligation as truth" exportedDependencyRejects
    , test "manifest must cover the trusted expected obligation set" missingExpectedObligationRejects
    , test "manifest identity is content-bound" manifestIdentityTamperRejects
    , test "append-only ledger extensions may add history" ledgerAppendPasses
    , test "append-only ledger history cannot be rewritten" ledgerMutationRejects
    , test "assurance-use content digests are checked" assuranceUseDigestRejects
    , test "retained runtime uses must cite RuntimeEnforced evidence" retainedRuntimeKindRejects
    ]
  if and results then pure () else exitFailure

referenceManifestVerifies :: Bool
referenceManifestVerifies =
  verifyManifest phase0UploadVerificationContext phase0UploadLedger phase0UploadManifest == Right ()

coreRevisionStable :: Bool
coreRevisionStable =
  revisionId first == revisionId second
    && revisionStatementDigest first == revisionStatementDigest second
  where
    first = coreRevision Truth
    second = coreRevision Truth

changedCoreClaimChangesRevision :: Bool
changedCoreClaimChangesRevision =
  revisionId (coreRevision Truth) /= revisionId (coreRevision Falsehood)

coreRevision :: Proposition -> ObligationRevision
coreRevision proposition = revisionFromCoreObligation
  Obligation
    { obligationId = ObligationId "test.core.handoff"
    , obligationProposition = proposition
    , obligationOrigin = "test"
    , obligationScope = "test.scope"
    , obligationRequiredPoint = "test.required"
    }
  "Test"
  "Core"
  ["subject"]
  ["context"]
  (AcceptEntry KernelChecked (EvidenceRole "establishes"))
  []

tamperedRevisionRejects :: Bool
tamperedRevisionRejects =
  case firstRevision phase0UploadLedger of
    Nothing -> False
    Just (key, revision) ->
      let badRevision = revision { revisionStatementDigest = digestText "tampered" }
          badLedger = phase0UploadLedger
            { ledgerRevisions = Map.insert key badRevision (ledgerRevisions phase0UploadLedger) }
          badManifest = sealManifest badLedger phase0UploadManifest
      in case verifyManifest phase0UploadVerificationContext badLedger badManifest of
          Left RevisionStatementDigestMismatch {} -> True
          _ -> False

missingRuntimeEvidenceRejects :: Bool
missingRuntimeEvidenceRejects =
  let entryId = EvidenceEntryId "evidence.upload.hello_policy.runtime"
      manifest = sealManifest phase0UploadLedger $
        phase0UploadManifest
          { manifestEvidenceEntries = Set.delete entryId (manifestEvidenceEntries phase0UploadManifest) }
  in case verifyManifest phase0UploadVerificationContext phase0UploadLedger manifest of
      Left (AcceptanceRuleUnsatisfied _) -> True
      _ -> False

unpermittedAssumptionRejects :: Bool
unpermittedAssumptionRejects =
  let assumptionKey = AssumptionId "assumption.runtime.receive_exact_contract"
      context = phase0UploadVerificationContext
        { verificationPermittedAssumptions =
            Set.delete assumptionKey (verificationPermittedAssumptions phase0UploadVerificationContext) }
  in case verifyManifest context phase0UploadLedger phase0UploadManifest of
      Left (UnpermittedAssumption key) -> key == assumptionKey
      _ -> False

staleValidityScopeRejects :: Bool
staleValidityScopeRejects =
  let changedValidity = Map.insert "architecture" "Other architecture"
        (verificationValidityContext phase0UploadVerificationContext)
      context = phase0UploadVerificationContext
        { verificationValidityContext = changedValidity }
      manifest0 = phase0UploadManifest { manifestValidityContext = changedValidity }
      manifest = sealManifest phase0UploadLedger manifest0
  in case verifyManifest context phase0UploadLedger manifest of
      Left EvidenceValidityScopeMismatch {} -> True
      Left AssumptionValidityScopeMismatch {} -> True
      _ -> False

missingCostReferenceRejects :: Bool
missingCostReferenceRejects =
  let missing = "upload.runtime.digest"
      context = phase0UploadVerificationContext
        { verificationKnownCostRefs =
            Set.delete missing (verificationKnownCostRefs phase0UploadVerificationContext) }
  in case verifyManifest context phase0UploadLedger phase0UploadManifest of
      Left (MissingCostReference _ costRef) -> costRef == missing
      _ -> False

rejectedEvidenceRejects :: Bool
rejectedEvidenceRejects =
  let entryId = EvidenceEntryId "evidence.upload.version.server.kernel"
      badLedger = adjustEvidence entryId
        (\entry -> entry { evidenceResult = EvidenceRejected "negative result" })
        phase0UploadLedger
      manifest = sealManifest badLedger phase0UploadManifest
  in case verifyManifest phase0UploadVerificationContext badLedger manifest of
      Left (SelectedRejectedEvidence key _) -> key == entryId
      _ -> False

emptyAcceptanceRuleRejects :: Bool
emptyAcceptanceRuleRejects =
  let revision0 = coreRevision Truth
      revision1 = revision0
        { revisionAcceptanceRule = AcceptAll []
        , revisionId = RevisionId ""
        }
      revision = revision1 { revisionId = deriveRevisionId revision1 }
      ledger = emptyLedger
        { ledgerRevisions = Map.singleton (revisionId revision) revision }
      manifest0 = emptyManifest
        { manifestArchitectureDigest = digestText "a"
        , manifestPhilCoreDigest = digestText "c"
        , manifestImplementationDigest = digestText "i"
        , manifestTarget = "test"
        , manifestCompilationProfile = "test"
        , manifestObligationRevisions = Set.singleton (revisionId revision)
        , manifestCertificationScope = Set.singleton (revisionId revision)
        , manifestLoweringLedgerRoot = digestText "l"
        }
      manifest = sealManifest ledger manifest0
      context = emptyVerificationContext
        { verificationArchitectureDigest = manifestArchitectureDigest manifest
        , verificationPhilCoreDigest = manifestPhilCoreDigest manifest
        , verificationImplementationDigest = manifestImplementationDigest manifest
        , verificationTarget = manifestTarget manifest
        , verificationCompilationProfile = manifestCompilationProfile manifest
        , verificationExpectedObligations = manifestObligationRevisions manifest
        , verificationLoweringLedgerRoot = manifestLoweringLedgerRoot manifest
        }
  in case verifyManifest context ledger manifest of
      Left (InvalidAcceptanceRule key) -> key == revisionId revision
      _ -> False

evidenceCycleRejects :: Bool
evidenceCycleRejects =
  let kernelId = EvidenceEntryId "evidence.upload.ingress.hello.kernel"
      runtimeId = EvidenceEntryId "evidence.upload.ingress.hello.runtime"
      ledger1 = adjustEvidence kernelId
        (\entry -> entry { evidenceDependsOn = [DependsOnEvidence runtimeId] })
        phase0UploadLedger
      ledger2 = adjustEvidence runtimeId
        (\entry -> entry { evidenceDependsOn = [DependsOnEvidence kernelId] })
        ledger1
      manifest = sealManifest ledger2 phase0UploadManifest
  in case verifyManifest phase0UploadVerificationContext ledger2 manifest of
      Left (JustificationCycle _) -> True
      _ -> False

requiredArtifactRejects :: Bool
requiredArtifactRejects =
  let entryId = EvidenceEntryId "evidence.upload.version.server.kernel"
      badLedger = adjustEvidence entryId
        (\entry -> entry { evidenceAssuranceKind = PropertyTested })
        phase0UploadLedger
      manifest = sealManifest badLedger phase0UploadManifest
  in case verifyManifest phase0UploadVerificationContext badLedger manifest of
      Left (EvidenceKindRequiresArtifact key PropertyTested) -> key == entryId
      _ -> False

artifactDigestMismatchRejects :: Bool
artifactDigestMismatchRejects =
  let entryId = EvidenceEntryId "evidence.upload.version.server.kernel"
      artifact = ArtifactIdentity (ArtifactRef "artifact:test") (digestText "declared")
      badLedger = adjustEvidence entryId
        (\entry -> entry
          { evidenceAssuranceKind = PropertyTested
          , evidenceArtifact = Just artifact
          })
        phase0UploadLedger
      context = phase0UploadVerificationContext
        { verificationAvailableArtifacts =
            Map.singleton (ArtifactRef "artifact:test") (digestText "actual") }
      manifest = sealManifest badLedger phase0UploadManifest
  in case verifyManifest context badLedger manifest of
      Left ArtifactDigestMismatch {} -> True
      _ -> False

missingExportRejects :: Bool
missingExportRejects =
  let revision = fixtureRevision "upload.version.unsupported_disjoint"
      manifest = sealManifest phase0UploadLedger $
        phase0UploadManifest
          { manifestCertificationScope = Set.delete revision (manifestCertificationScope phase0UploadManifest) }
  in case verifyManifest phase0UploadVerificationContext phase0UploadLedger manifest of
      Left (OutOfScopeObligationNotExported key) -> key == revision
      _ -> False

permittedExportPasses :: Bool
permittedExportPasses =
  let revision = fixtureRevision "upload.version.unsupported_disjoint"
      export = mkExport "export.upload.unsupported" revision "parent.component"
      ledger = phase0UploadLedger
        { ledgerExports = Map.singleton (exportId export) export }
      manifest0 = phase0UploadManifest
        { manifestCertificationScope = Set.delete revision (manifestCertificationScope phase0UploadManifest)
        , manifestExports = Set.singleton (exportId export)
        }
      manifest = sealManifest ledger manifest0
      context = phase0UploadVerificationContext
        { verificationPermittedExportBoundaries = Set.singleton "parent.component" }
  in verifyManifest context ledger manifest == Right ()

unpermittedExportRejects :: Bool
unpermittedExportRejects =
  let revision = fixtureRevision "upload.version.unsupported_disjoint"
      export = mkExport "export.upload.unsupported" revision "parent.component"
      ledger = phase0UploadLedger
        { ledgerExports = Map.singleton (exportId export) export }
      manifest = sealManifest ledger $
        phase0UploadManifest
          { manifestCertificationScope = Set.delete revision (manifestCertificationScope phase0UploadManifest)
          , manifestExports = Set.singleton (exportId export)
          }
  in case verifyManifest phase0UploadVerificationContext ledger manifest of
      Left (UnpermittedExportBoundary key _) -> key == exportId export
      _ -> False

exportedDependencyRejects :: Bool
exportedDependencyRejects =
  let revision = fixtureRevision "upload.digest.matches"
      export = mkExport "export.upload.digest" revision "parent.component"
      ledger = phase0UploadLedger
        { ledgerExports = Map.singleton (exportId export) export }
      manifest = sealManifest ledger $
        phase0UploadManifest
          { manifestCertificationScope = Set.delete revision (manifestCertificationScope phase0UploadManifest)
          , manifestExports = Set.singleton (exportId export)
          }
      context = phase0UploadVerificationContext
        { verificationPermittedExportBoundaries = Set.singleton "parent.component" }
  in case verifyManifest context ledger manifest of
      Left DependencyOnExportedObligation {} -> True
      _ -> False

missingExpectedObligationRejects :: Bool
missingExpectedObligationRejects =
  let revision = fixtureRevision "upload.version.unsupported_disjoint"
      manifest = sealManifest phase0UploadLedger $
        phase0UploadManifest
          { manifestObligationRevisions = Set.delete revision (manifestObligationRevisions phase0UploadManifest)
          , manifestCertificationScope = Set.delete revision (manifestCertificationScope phase0UploadManifest)
          }
  in case verifyManifest phase0UploadVerificationContext phase0UploadLedger manifest of
      Left ExpectedObligationSetMismatch {} -> True
      _ -> False

manifestIdentityTamperRejects :: Bool
manifestIdentityTamperRejects =
  let manifest = phase0UploadManifest { manifestId = digestText "tampered manifest" }
  in case verifyManifest phase0UploadVerificationContext phase0UploadLedger manifest of
      Left ManifestIdentityMismatch {} -> True
      _ -> False

ledgerAppendPasses :: Bool
ledgerAppendPasses =
  let assumption = mkTestAssumption "assumption.test.added" "new assumption"
      next = phase0UploadLedger
        { ledgerAssumptions = Map.insert
            (assumptionId assumption)
            assumption
            (ledgerAssumptions phase0UploadLedger) }
  in verifyLedgerExtension phase0UploadLedger next == Right ()

ledgerMutationRejects :: Bool
ledgerMutationRejects =
  let key = AssumptionId "assumption.runtime.storage_contract"
      next = phase0UploadLedger
        { ledgerAssumptions = Map.adjust
            (\assumption -> assumption { assumptionStatement = "rewritten history" })
            key
            (ledgerAssumptions phase0UploadLedger) }
  in case verifyLedgerExtension phase0UploadLedger next of
      Left (LedgerHistoryMutation "assumption") -> True
      _ -> False

assuranceUseDigestRejects :: Bool
assuranceUseDigestRejects =
  case Map.lookup useId (ledgerUses phase0UploadLedger) of
    Nothing -> False
    Just assuranceUse ->
      let badUse = setUseDigest (digestText "tampered use") assuranceUse
          badLedger = phase0UploadLedger
            { ledgerUses = Map.insert useId badUse (ledgerUses phase0UploadLedger) }
          manifest = sealManifest badLedger phase0UploadManifest
      in case verifyManifest phase0UploadVerificationContext badLedger manifest of
          Left (AssuranceUseDigestMismatch key _ _) -> key == useId
          _ -> False
  where
    useId = AssuranceUseId "use.upload.hello_ingress"

retainedRuntimeKindRejects :: Bool
retainedRuntimeKindRejects =
  case Map.lookup useId (ledgerUses phase0UploadLedger) of
    Just RetainedRuntimeUse {} ->
      let badUse0 = RetainedRuntimeUse
            { assuranceUseId = useId
            , assuranceUseDigest = Digest ""
            , useObligationRevision = fixtureRevision "upload.ingress.hello.complete_recognition"
            , useRuntimeEvidence = EvidenceEntryId "evidence.upload.ingress.hello.kernel"
            , useCostRef = "upload.runtime.frame_receive"
            }
          badUse = badUse0 { assuranceUseDigest = deriveAssuranceUseDigest badUse0 }
          badLedger = phase0UploadLedger
            { ledgerUses = Map.insert useId badUse (ledgerUses phase0UploadLedger) }
          manifest = sealManifest badLedger phase0UploadManifest
      in case verifyManifest phase0UploadVerificationContext badLedger manifest of
          Left (RuntimeUseRequiresRuntimeEvidence key _) -> key == useId
          _ -> False
    _ -> False
  where
    useId = AssuranceUseId "use.upload.hello_ingress"

sealManifest :: AssuranceLedger -> AssuranceManifest -> AssuranceManifest
sealManifest ledger manifest = manifest { manifestId = deriveManifestId ledger manifest }

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

mkExport :: Text -> RevisionId -> Text -> ExportEntry
mkExport stableId revision boundary = provisional
  { exportDigest = deriveExportDigest provisional }
  where
    provisional = ExportEntry
      { exportId = ExportId stableId
      , exportDigest = Digest ""
      , exportObligationRevision = revision
      , exportDestinationBoundary = boundary
      , exportDerivedObligationId = ObligationId ("exported." <> stableId)
      , exportValidityScope = ValidityScope Map.empty
      }

mkTestAssumption :: Text -> Text -> Assumption
mkTestAssumption stableId statement = provisional
  { assumptionDigest = deriveAssumptionDigest provisional }
  where
    provisional = Assumption
      { assumptionId = AssumptionId stableId
      , assumptionDigest = Digest ""
      , assumptionStatement = statement
      , assumptionScope = "test"
      , assumptionOwnerBoundary = "test"
      , assumptionRationale = "test"
      , assumptionValidityScope = ValidityScope Map.empty
      }

fixtureRevision :: Text -> RevisionId
fixtureRevision obligationName =
  case
    [ revisionId revision
    | revision <- Map.elems (ledgerRevisions phase0UploadLedger)
    , revisionObligationId revision == ObligationId obligationName
    ] of
      revision : _ -> revision
      [] -> RevisionId "<missing-fixture-revision>"

firstRevision :: AssuranceLedger -> Maybe (RevisionId, ObligationRevision)
firstRevision ledger = case Map.toAscList (ledgerRevisions ledger) of
  pair : _ -> Just pair
  [] -> Nothing

setUseDigest :: Digest -> AssuranceUse -> AssuranceUse
setUseDigest digest assuranceUse = case assuranceUse of
  ErasureUse useId _ revision entries -> ErasureUse useId digest revision entries
  RetainedRuntimeUse useId _ revision entry costRef ->
    RetainedRuntimeUse useId digest revision entry costRef

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
