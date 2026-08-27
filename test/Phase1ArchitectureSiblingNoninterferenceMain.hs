{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
import Phil.Assurance.ArchitectureIdentity
  ( interfaceValidityContext
  , interfaceValidityScope
  )
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor (..)
  , ArchitectureInstanceIdentity (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , SemanticForm (..)
  , deriveArchitectureInstanceIdentity
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
    [ test "edited child revises only its own declaration identity" editedChildRevises
    , test "edited child revises parent definition without revising parent interface" parentDefinitionRevises
    , test "unaffected sibling declaration identity remains exact" siblingDeclarationStable
    , test "unaffected sibling instance identity survives parent revision" siblingInstanceStable
    , test "unaffected sibling interface evidence remains valid after peer edit" siblingEvidenceRemainsValid
    , test "old evidence for edited child invalidates after its interface revision" editedChildOldEvidenceRejects
    , test "fresh evidence for edited child verifies after revision" editedChildFreshEvidenceVerifies
    ]
  if and results then pure () else exitFailure

storeIdentity :: DeclarationIdentity
storeIdentity = deriveDeclarationIdentity storeDescriptor

metricsBeforeIdentity :: DeclarationIdentity
metricsBeforeIdentity = deriveDeclarationIdentity metricsBeforeDescriptor

metricsAfterIdentity :: DeclarationIdentity
metricsAfterIdentity = deriveDeclarationIdentity metricsAfterDescriptor

parentBeforeIdentity :: DeclarationIdentity
parentBeforeIdentity = deriveDeclarationIdentity
  (parentDescriptor storeIdentity metricsBeforeIdentity)

parentAfterIdentity :: DeclarationIdentity
parentAfterIdentity = deriveDeclarationIdentity
  (parentDescriptor storeIdentity metricsAfterIdentity)

storeDescriptor :: DeclarationDescriptor
storeDescriptor = DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "store" ["Steve"]
  , declarationKey = DeclarationKey "architecture.steve.store"
  , declarationInterfaceSemantics = SemanticRecord (Map.fromList
      [ ("provider", SemanticAtom "BlobProvider")
      , ("authority", SemanticAtom "read-write")
      ])
  , declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("algorithm", SemanticAtom "install-if-absent-v1")
      , ("cleanup", SemanticAtom "release-on-all-failures")
      ])
  }

metricsBeforeDescriptor :: DeclarationDescriptor
metricsBeforeDescriptor = DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "metrics" ["Steve"]
  , declarationKey = DeclarationKey "architecture.steve.metrics"
  , declarationInterfaceSemantics = SemanticRecord (Map.fromList
      [ ("provider", SemanticAtom "MetricsProvider")
      , ("events", SemanticUnordered (Set.fromList
          [ SemanticAtom "put"
          , SemanticAtom "get"
          ]))
      ])
  , declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("sink", SemanticAtom "counter-v1")
      ])
  }

metricsAfterDescriptor :: DeclarationDescriptor
metricsAfterDescriptor = metricsBeforeDescriptor
  { declarationInterfaceSemantics = SemanticRecord (Map.fromList
      [ ("provider", SemanticAtom "MetricsProvider")
      , ("events", SemanticUnordered (Set.fromList
          [ SemanticAtom "put"
          , SemanticAtom "get"
          , SemanticAtom "miss"
          ]))
      ])
  , declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("sink", SemanticAtom "counter-v2")
      ])
  }

parentDescriptor
  :: DeclarationIdentity
  -> DeclarationIdentity
  -> DeclarationDescriptor
parentDescriptor store metrics = DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "steve" ["Steve"]
  , declarationKey = DeclarationKey "architecture.steve"
  , declarationInterfaceSemantics = SemanticAtom "SteveArchitecture"
  , declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("store", SemanticAtom
          (unDefinitionRevision (identityDefinitionRevision store)))
      , ("metrics", SemanticAtom
          (unDefinitionRevision (identityDefinitionRevision metrics)))
      ])
  }

storeInstance :: DeclarationIdentity -> ArchitectureInstanceIdentity
storeInstance declaration = deriveArchitectureInstanceIdentity ArchitectureInstanceDescriptor
  { architectureInstanceKey = InstanceKey "steve.store"
  , architectureParentInstanceKey = Just (InstanceKey "steve")
  , architectureDeclarationIdentity = declaration
  , architectureStaticBindings = Map.empty
  }

editedChildRevises :: Bool
editedChildRevises =
  identityDeclarationKey metricsBeforeIdentity == identityDeclarationKey metricsAfterIdentity
    && identityInterfaceRevision metricsBeforeIdentity /= identityInterfaceRevision metricsAfterIdentity
    && identityDefinitionRevision metricsBeforeIdentity /= identityDefinitionRevision metricsAfterIdentity

parentDefinitionRevises :: Bool
parentDefinitionRevises =
  identityInterfaceRevision parentBeforeIdentity == identityInterfaceRevision parentAfterIdentity
    && identityDefinitionRevision parentBeforeIdentity /= identityDefinitionRevision parentAfterIdentity

siblingDeclarationStable :: Bool
siblingDeclarationStable =
  deriveDeclarationIdentity storeDescriptor == storeIdentity

siblingInstanceStable :: Bool
siblingInstanceStable =
  storeInstance storeIdentity == storeInstance (deriveDeclarationIdentity storeDescriptor)
    && identityDefinitionRevision parentBeforeIdentity /= identityDefinitionRevision parentAfterIdentity

siblingEvidenceRemainsValid :: Bool
siblingEvidenceRemainsValid =
  verifyFor
    parentAfterIdentity
    [storeIdentity, metricsAfterIdentity]
    (mkEvidence "evidence.arch.store.interface" storeIdentity)
    == Right ()

editedChildOldEvidenceRejects :: Bool
editedChildOldEvidenceRejects =
  let stale = mkEvidence "evidence.arch.metrics.old-interface" metricsBeforeIdentity
  in case verifyFor parentAfterIdentity [storeIdentity, metricsAfterIdentity] stale of
      Left (EvidenceValidityScopeMismatch key) -> key == evidenceEntryId stale
      _ -> False

editedChildFreshEvidenceVerifies :: Bool
editedChildFreshEvidenceVerifies =
  verifyFor
    parentAfterIdentity
    [storeIdentity, metricsAfterIdentity]
    (mkEvidence "evidence.arch.metrics.new-interface" metricsAfterIdentity)
    == Right ()

interfaceObligation :: ObligationRevision
interfaceObligation = revisionFromCoreObligation
  Obligation
    { obligationId = ObligationId "architecture.sibling.interface-law"
    , obligationProposition = Truth
    , obligationOrigin = "ARCH-007 fixture"
    , obligationScope = "architecture.steve"
    , obligationRequiredPoint = "architecture admission"
    }
  "ArchitectureInterface"
  "Core"
  ["architecture.steve"]
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
      , evidenceProducer = "Phase1ArchitectureSiblingNoninterferenceMain"
      , evidenceChecker = "Phil.Core.Static / Phil.Assurance.Verify"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = interfaceValidityScope identity
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = ["exact declaration interface"]
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

verifyFor
  :: DeclarationIdentity
  -> [DeclarationIdentity]
  -> EvidenceEntry
  -> Either ManifestError ()
verifyFor parent siblings evidence = verifyManifest context ledger manifest
  where
    revisionKey = revisionId interfaceObligation
    validity = Map.unions (map interfaceValidityContext siblings)
    ledger = emptyLedger
      { ledgerRevisions = Map.singleton revisionKey interfaceObligation
      , ledgerEvidence = Map.singleton (evidenceEntryId evidence) evidence
      }
    manifest0 = emptyManifest
      { manifestArchitectureDigest = digestText
          (unDefinitionRevision (identityDefinitionRevision parent))
      , manifestPhilCoreDigest = digestText "phase1.arch-sibling.core"
      , manifestImplementationDigest = digestText "phase1.arch-sibling.impl"
      , manifestTarget = "host"
      , manifestCompilationProfile = "phase1.arch-sibling"
      , manifestObligationRevisions = Set.singleton revisionKey
      , manifestCertificationScope = Set.singleton revisionKey
      , manifestEvidenceEntries = Set.singleton (evidenceEntryId evidence)
      , manifestLoweringLedgerRoot = digestText "phase1.arch-sibling.no-lowering"
      , manifestValidityContext = validity
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
      , verificationValidityContext = validity
      }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
