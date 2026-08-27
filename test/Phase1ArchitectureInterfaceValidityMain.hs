{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
import Phil.Assurance.ArchitectureIdentity
  ( interfaceValidityContext
  , interfaceValidityDimension
  , interfaceValidityScope
  )
import Phil.Core.Static
  ( DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  , deriveDeclarationIdentity
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (Truth)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "public contract change preserves DeclarationKey and revises InterfaceRevision" publicContractRevises
    , test "interface validity dimension follows stable declaration lineage" validityDimensionFollowsLineage
    , test "evidence scoped to the current interface revision verifies" currentInterfaceEvidenceVerifies
    , test "old interface-scoped evidence rejects after public contract revision" staleInterfaceEvidenceRejects
    , test "fresh evidence for the revised public interface verifies" revisedInterfaceEvidenceVerifies
    , test "definition-only replacement preserves interface-scoped evidence validity" definitionOnlyReplacementPreservesEvidence
    ]
  if and results then pure () else exitFailure

originalIdentity :: DeclarationIdentity
originalIdentity = deriveDeclarationIdentity originalDescriptor

revisedInterfaceIdentity :: DeclarationIdentity
revisedInterfaceIdentity = deriveDeclarationIdentity revisedInterfaceDescriptor

definitionOnlyIdentity :: DeclarationIdentity
definitionOnlyIdentity = deriveDeclarationIdentity definitionOnlyDescriptor

originalDescriptor :: DeclarationDescriptor
originalDescriptor = DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "blob" ["Steve"]
  , declarationKey = DeclarationKey "provider.blob"
  , declarationInterfaceSemantics = SemanticRecord (Map.fromList
      [ ("provider", SemanticAtom "BlobProvider")
      , ("authority", SemanticAtom "read-write")
      ])
  , declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("algorithm", SemanticAtom "install-if-absent-v1")
      , ("cleanup", SemanticAtom "release-on-all-failures")
      ])
  }

revisedInterfaceDescriptor :: DeclarationDescriptor
revisedInterfaceDescriptor = originalDescriptor
  { declarationInterfaceSemantics = SemanticRecord (Map.fromList
      [ ("provider", SemanticAtom "BlobProvider")
      , ("authority", SemanticAtom "read-write")
      , ("failure", SemanticAtom "explicit")
      ])
  }

definitionOnlyDescriptor :: DeclarationDescriptor
definitionOnlyDescriptor = originalDescriptor
  { declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("algorithm", SemanticAtom "install-if-absent-v2")
      , ("cleanup", SemanticAtom "release-on-all-failures")
      ])
  }

publicContractRevises :: Bool
publicContractRevises =
  identityDeclarationKey originalIdentity == identityDeclarationKey revisedInterfaceIdentity
    && identityInterfaceRevision originalIdentity /= identityInterfaceRevision revisedInterfaceIdentity
    && identityDefinitionRevision originalIdentity /= identityDefinitionRevision revisedInterfaceIdentity

validityDimensionFollowsLineage :: Bool
validityDimensionFollowsLineage =
  interfaceValidityDimension originalIdentity
    == interfaceValidityDimension revisedInterfaceIdentity
    && interfaceValidityContext originalIdentity
      /= interfaceValidityContext revisedInterfaceIdentity

currentInterfaceEvidenceVerifies :: Bool
currentInterfaceEvidenceVerifies =
  verifyFor originalIdentity (mkEvidence "evidence.arch.interface.original" originalIdentity)
    == Right ()

staleInterfaceEvidenceRejects :: Bool
staleInterfaceEvidenceRejects =
  let stale = mkEvidence "evidence.arch.interface.original" originalIdentity
  in case verifyFor revisedInterfaceIdentity stale of
      Left (EvidenceValidityScopeMismatch key) -> key == evidenceEntryId stale
      _ -> False

revisedInterfaceEvidenceVerifies :: Bool
revisedInterfaceEvidenceVerifies =
  verifyFor revisedInterfaceIdentity
    (mkEvidence "evidence.arch.interface.revised" revisedInterfaceIdentity)
    == Right ()

definitionOnlyReplacementPreservesEvidence :: Bool
definitionOnlyReplacementPreservesEvidence =
  identityInterfaceRevision originalIdentity == identityInterfaceRevision definitionOnlyIdentity
    && identityDefinitionRevision originalIdentity /= identityDefinitionRevision definitionOnlyIdentity
    && verifyFor definitionOnlyIdentity
      (mkEvidence "evidence.arch.interface.original" originalIdentity)
      == Right ()

interfaceObligation :: ObligationRevision
interfaceObligation = revisionFromCoreObligation
  Obligation
    { obligationId = ObligationId "architecture.provider.blob.interface-law"
    , obligationProposition = Truth
    , obligationOrigin = "ARCH-003 fixture"
    , obligationScope = "provider.blob"
    , obligationRequiredPoint = "architecture admission"
    }
  "ArchitectureInterface"
  "Core"
  ["provider.blob"]
  []
  (AcceptEntry KernelChecked (EvidenceRole "establishes"))
  []

mkEvidence :: Text -> DeclarationIdentity -> EvidenceEntry
mkEvidence stableId identity = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId stableId
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId interfaceObligation
      , evidenceAssuranceKind = KernelChecked
      , evidenceRole = EvidenceRole "establishes"
      , evidenceProducer = "Phase1ArchitectureInterfaceValidityMain"
      , evidenceChecker = "Phil.Core.Static / Phil.Assurance.Verify"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = interfaceValidityScope identity
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = ["exact public interface contract"]
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

verifyFor :: DeclarationIdentity -> EvidenceEntry -> Either ManifestError ()
verifyFor identity evidence = verifyManifest context ledger manifest
  where
    revisionKey = revisionId interfaceObligation
    ledger = emptyLedger
      { ledgerRevisions = Map.singleton revisionKey interfaceObligation
      , ledgerEvidence = Map.singleton (evidenceEntryId evidence) evidence
      }
    manifest0 = emptyManifest
      { manifestArchitectureDigest = architectureDigest identity
      , manifestPhilCoreDigest = digestText "phase1.arch-id.core"
      , manifestImplementationDigest = digestText "phase1.arch-id.impl"
      , manifestTarget = "host"
      , manifestCompilationProfile = "phase1.arch-id"
      , manifestObligationRevisions = Set.singleton revisionKey
      , manifestCertificationScope = Set.singleton revisionKey
      , manifestEvidenceEntries = Set.singleton (evidenceEntryId evidence)
      , manifestLoweringLedgerRoot = digestText "phase1.arch-id.no-lowering"
      , manifestValidityContext = interfaceValidityContext identity
      }
    manifest = manifest0 { manifestId = deriveManifestId ledger manifest0 }
    context = emptyVerificationContext
      { verificationArchitectureDigest = manifestArchitectureDigest manifest
      , verificationPhilCoreDigest = manifestPhilCoreDigest manifest
      , verificationImplementationDigest = manifestImplementationDigest manifest
      , verificationTarget = manifestTarget manifest
      , verificationCompilationProfile = manifestCompilationProfile manifest
      , verificationExpectedObligations = manifestObligationRevisions manifest
      , verificationLoweringLedgerRoot = manifestLoweringLedgerRoot manifest
      , verificationValidityContext = manifestValidityContext manifest
      }

architectureDigest :: DeclarationIdentity -> Digest
architectureDigest identity = digestText
  (declarationKeyText (identityDeclarationKey identity)
    <> "|"
    <> interfaceText (identityInterfaceRevision identity)
    <> "|"
    <> definitionText (identityDefinitionRevision identity))

declarationKeyText :: DeclarationKey -> Text
declarationKeyText (DeclarationKey value) = value

interfaceText :: InterfaceRevision -> Text
interfaceText (InterfaceRevision value) = value

definitionText :: DefinitionRevision -> Text
definitionText (DefinitionRevision value) = value

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
