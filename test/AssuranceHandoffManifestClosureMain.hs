{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance
import Phil.Core.Decision
  ( AssumptionRef (..)
  , DecisionCertificate (..)
  )
import Phil.Core.Discharge
  ( ObligationDisposition (..)
  , ResolvedObligation (..)
  , StaticDischarge (..)
  )
import Phil.Core.Syntax
  ( Name (..)
  , Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  )
import Phil.Verification
import Phil.Verification.Bundle
import Phil.Verification.ManifestClosure
import System.Exit (exitFailure)

data Fixture = Fixture
  { fixtureEntries :: [LedgerHandoff]
  , fixtureGraph :: VerificationObligationGraph
  , fixtureBundle :: VerificationBundle
  , fixturePolicy :: ApplicationAssurancePolicy
  , fixtureContext :: VerificationContext
  , fixtureLedger :: AssuranceLedger
  , fixtureSelection :: ManifestClosureSelection
  , fixtureHandoff :: ManifestClosureHandoff
  , fixtureParentRevision :: RevisionId
  , fixtureChildRevision :: RevisionId
  , fixtureParentEvidenceId :: EvidenceEntryId
  , fixtureSupportEvidenceId :: EvidenceEntryId
  }

main :: IO ()
main = do
  results <- sequence
    [ test "INT-002 closes exact handoff-bound certificate evidence" happyPath
    , test "INT-002 rejects certificate evidence that drops prerequisite support"
        missingPrerequisiteSupportRejected
    , test "INT-002 rejects certificate evidence that drops precise EvidenceFact support"
        missingEvidenceFactSupportRejected
    , test "INT-002 rejects a bundle graph that omits handoff prerequisite support"
        graphSupportMismatchRejected
    , test "INT-002 requires an evidence binding for every certificate handoff"
        missingCertificateBindingRejected
    , test "INT-002 rejects a certificate binding to the wrong evidence revision"
        wrongCertificateEvidenceRejected
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

happyPath :: Either String ()
happyPath = do
  fixture <- baseFixture
  _ <- mapLeft show (closeFixture fixture)
  Right ()

missingPrerequisiteSupportRejected :: Either String ()
missingPrerequisiteSupportRejected = do
  fixture <- baseFixture
  parent <- parentEvidence fixture
  let mutated = sealEvidence parent
        { evidenceDependsOn =
            [ DependsOnEvidence (fixtureSupportEvidenceId fixture) ]
        }
  changed <- rebuildEvidence fixture mutated
  case closeFixture changed of
    Left (ManifestClosureHandoffEvidenceMismatch revision entryId)
      | revision == fixtureParentRevision fixture
      , entryId == fixtureParentEvidenceId fixture -> Right ()
    other -> Left ("expected handoff evidence mismatch, got " <> show other)

missingEvidenceFactSupportRejected :: Either String ()
missingEvidenceFactSupportRejected = do
  fixture <- baseFixture
  parent <- parentEvidence fixture
  let mutated = sealEvidence parent
        { evidenceDependsOn =
            [ DependsOnObligation (fixtureChildRevision fixture) ]
        }
  changed <- rebuildEvidence fixture mutated
  case closeFixture changed of
    Left (ManifestClosureHandoffEvidenceMismatch revision entryId)
      | revision == fixtureParentRevision fixture
      , entryId == fixtureParentEvidenceId fixture -> Right ()
    other -> Left ("expected handoff evidence mismatch, got " <> show other)

graphSupportMismatchRejected :: Either String ()
graphSupportMismatchRejected = do
  fixture <- baseFixture
  graph <- mapLeft show $ buildVerificationRevisionGraphWithSupport
    (map handoffRevision (fixtureEntries fixture))
    Set.empty
    (verificationGraphCertificationScope (fixtureGraph fixture))
  changed <- rebuildGraph fixture graph
  let expected = Set.singleton
        (fixtureParentRevision fixture, fixtureChildRevision fixture)
  case closeFixture changed of
    Left (ManifestClosureHandoffSupportMismatch actualExpected actualGraph)
      | actualExpected == expected
      , Set.null actualGraph -> Right ()
    other -> Left ("expected exact handoff support mismatch, got " <> show other)

missingCertificateBindingRejected :: Either String ()
missingCertificateBindingRejected = do
  fixture <- baseFixture
  let handoff = (fixtureHandoff fixture)
        { manifestClosureCertificateEvidence = Map.empty }
      changed = fixture { fixtureHandoff = handoff }
      expected = Set.singleton (fixtureParentRevision fixture)
  case closeFixture changed of
    Left (ManifestClosureHandoffEvidenceDomainMismatch actual supplied)
      | actual == expected
      , Set.null supplied -> Right ()
    other -> Left ("expected certificate evidence-domain mismatch, got " <> show other)

wrongCertificateEvidenceRejected :: Either String ()
wrongCertificateEvidenceRejected = do
  fixture <- baseFixture
  let handoff = (fixtureHandoff fixture)
        { manifestClosureCertificateEvidence = Map.singleton
            (fixtureParentRevision fixture)
            (fixtureSupportEvidenceId fixture)
        }
      changed = fixture { fixtureHandoff = handoff }
  case closeFixture changed of
    Left (ManifestClosureHandoffEvidenceRejected revision entryId
        (HandoffEvidenceRevisionMismatch expected actual))
      | revision == fixtureParentRevision fixture
      , entryId == fixtureSupportEvidenceId fixture
      , expected == fixtureParentRevision fixture
      , actual == fixtureChildRevision fixture -> Right ()
    other -> Left ("expected evidence revision mismatch, got " <> show other)

closeFixture :: Fixture -> Either ManifestClosureError AssuranceManifest
closeFixture fixture = closeVerificationBundleWithHandoff
  (fixtureBundle fixture)
  (fixturePolicy fixture)
  (fixtureContext fixture)
  (fixtureLedger fixture)
  (fixtureSelection fixture)
  (fixtureHandoff fixture)

baseFixture :: Either String Fixture
baseFixture = do
  entries <- mapLeft show $ handoffResolvedObligationWithEvidence
    handoffConfig
    (Map.singleton (evidenceName, evidenceIndex) supportEvidenceId)
    mixedResolved
  (parent, child) <- case entries of
    [parentEntry, childEntry] -> Right (parentEntry, childEntry)
    other -> Left ("expected parent/child handoff, got " <> show other)
  let parentRevision = revisionId (handoffRevision parent)
      childRevision = revisionId (handoffRevision child)
      scope = Set.fromList [parentRevision, childRevision]
  graph <- mapLeft show $ buildVerificationRevisionGraphWithSupport
    (map handoffRevision entries)
    (handoffSupportEdges entries)
    scope
  let supportEvidenceEntry = sealEvidence (mkSupportEvidence childRevision)
      provisionalParent = mkParentEvidence parentRevision
  parentEvidenceValue <- mapLeft show $
    bindHandoffCertificateEvidence parent provisionalParent
  let policy = ApplicationAssurancePolicy
        { applicationAssurancePolicyRevision = AssurancePolicyRevision
            "audit-handoff-manifest-v1"
        , applicationAssurancePolicyPermittedDispositions =
            Set.singleton Phil.Verification.StaticallyDischarged
        }
  bundle <- mapLeft show $ buildVerificationBundle
    (digestText "audit-handoff-manifest-source")
    [] [] []
    graph
    policy
    [parentEvidenceValue, supportEvidenceEntry]
  let ledger = emptyLedger
        { ledgerRevisions = verificationGraphNodes graph
        , ledgerEvidence = Map.fromList
            [ (evidenceEntryId parentEvidenceValue, parentEvidenceValue)
            , (evidenceEntryId supportEvidenceEntry, supportEvidenceEntry)
            ]
        }
      context = emptyVerificationContext
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationPhilCoreDigest = digestText "audit-handoff-manifest-core"
        , verificationImplementationDigest = digestText "audit-handoff-manifest-impl"
        , verificationTarget = "audit-handoff-manifest-target"
        , verificationCompilationProfile = "checked-runtime"
        , verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        , verificationLoweringLedgerRoot = digestText "audit-handoff-manifest-lowering"
        }
      selection = ManifestClosureSelection
        { manifestClosureEvidence = Set.fromList
            [ parentEvidenceId
            , supportEvidenceId
            ]
        , manifestClosureAssumptions = Set.empty
        , manifestClosureExports = Map.empty
        , manifestClosureUses = Set.empty
        }
      handoff = ManifestClosureHandoff
        { manifestClosureHandoffEntries = entries
        , manifestClosureCertificateEvidence = Map.singleton
            parentRevision parentEvidenceId
        }
  Right Fixture
    { fixtureEntries = entries
    , fixtureGraph = graph
    , fixtureBundle = bundle
    , fixturePolicy = policy
    , fixtureContext = context
    , fixtureLedger = ledger
    , fixtureSelection = selection
    , fixtureHandoff = handoff
    , fixtureParentRevision = parentRevision
    , fixtureChildRevision = childRevision
    , fixtureParentEvidenceId = parentEvidenceId
    , fixtureSupportEvidenceId = supportEvidenceId
    }

rebuildEvidence :: Fixture -> EvidenceEntry -> Either String Fixture
rebuildEvidence fixture replacement = do
  support <- supportEvidence fixture
  bundle <- mapLeft show $ buildVerificationBundle
    (digestText "audit-handoff-manifest-source")
    [] [] []
    (fixtureGraph fixture)
    (fixturePolicy fixture)
    [replacement, support]
  let ledger0 = fixtureLedger fixture
      ledger = ledger0
        { ledgerEvidence = Map.insert
            (fixtureParentEvidenceId fixture)
            replacement
            (ledgerEvidence ledger0)
        }
      context = (fixtureContext fixture)
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle }
  Right fixture
    { fixtureBundle = bundle
    , fixtureLedger = ledger
    , fixtureContext = context
    }

rebuildGraph :: Fixture -> VerificationObligationGraph -> Either String Fixture
rebuildGraph fixture graph = do
  parent <- parentEvidence fixture
  support <- supportEvidence fixture
  bundle <- mapLeft show $ buildVerificationBundle
    (digestText "audit-handoff-manifest-source")
    [] [] []
    graph
    (fixturePolicy fixture)
    [parent, support]
  let ledger0 = fixtureLedger fixture
      ledger = ledger0 { ledgerRevisions = verificationGraphNodes graph }
      context = (fixtureContext fixture)
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        }
  Right fixture
    { fixtureGraph = graph
    , fixtureBundle = bundle
    , fixtureLedger = ledger
    , fixtureContext = context
    }

parentEvidence :: Fixture -> Either String EvidenceEntry
parentEvidence fixture =
  case Map.lookup (fixtureParentEvidenceId fixture)
      (ledgerEvidence (fixtureLedger fixture)) of
    Nothing -> Left "parent evidence missing from fixture ledger"
    Just value -> Right value

supportEvidence :: Fixture -> Either String EvidenceEntry
supportEvidence fixture =
  case Map.lookup (fixtureSupportEvidenceId fixture)
      (ledgerEvidence (fixtureLedger fixture)) of
    Nothing -> Left "support evidence missing from fixture ledger"
    Just value -> Right value

mkParentEvidence :: RevisionId -> EvidenceEntry
mkParentEvidence revision = EvidenceEntry
  { evidenceEntryId = parentEvidenceId
  , evidenceEntryDigest = Digest "unbound-before-handoff"
  , evidenceObligationRevision = revision
  , evidenceAssuranceKind = KernelChecked
  , evidenceRole = EvidenceRole "certificate"
  , evidenceProducer = "Phil Core certificate checker"
  , evidenceChecker = "Phil Core"
  , evidenceArtifact = Nothing
  , evidenceInputDigests = []
  , evidenceAssumptions = []
  , evidenceDependsOn = []
  , evidenceValidityScope = ValidityScope Map.empty
  , evidenceResult = EvidenceAccepted
  , evidenceJustifies = ["checked decision certificate"]
  , evidenceRuntimeMechanism = Nothing
  , evidenceRuntimeResidue = []
  , evidenceCostRefs = []
  }

mkSupportEvidence :: RevisionId -> EvidenceEntry
mkSupportEvidence revision = EvidenceEntry
  { evidenceEntryId = supportEvidenceId
  , evidenceEntryDigest = Digest ""
  , evidenceObligationRevision = revision
  , evidenceAssuranceKind = KernelChecked
  , evidenceRole = EvidenceRole "support"
  , evidenceProducer = "authoritative EvidenceFact source"
  , evidenceChecker = "Phil Core"
  , evidenceArtifact = Nothing
  , evidenceInputDigests = []
  , evidenceAssumptions = []
  , evidenceDependsOn = []
  , evidenceValidityScope = ValidityScope Map.empty
  , evidenceResult = EvidenceAccepted
  , evidenceJustifies = ["immutable EvidenceFact support"]
  , evidenceRuntimeMechanism = Nothing
  , evidenceRuntimeResidue = []
  , evidenceCostRefs = []
  }

sealEvidence :: EvidenceEntry -> EvidenceEntry
sealEvidence entry = entry { evidenceEntryDigest = deriveEvidenceEntryDigest entry }

parentEvidenceId :: EvidenceEntryId
parentEvidenceId = EvidenceEntryId "evidence.audit.handoff.parent"

supportEvidenceId :: EvidenceEntryId
supportEvidenceId = EvidenceEntryId "evidence.audit.handoff.fact"

evidenceName :: Name
evidenceName = Name "proof"

evidenceIndex :: Int
evidenceIndex = 1

mixedResolved :: ResolvedObligation
mixedResolved = ResolvedObligation
  { resolvedObligation = parentObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = [childResolved]
  , resolvedDisposition = Phil.Core.Discharge.StaticallyDischarged StaticByCertificate
      { staticCertificateProducer = "test-producer"
      , staticCertificateChecker = "test-checker"
      , staticCertificate = CertificateConjunction
          (CertificateAssumption (EvidenceFact evidenceName evidenceIndex) Truth)
          (CertificateAssumption
            (PrerequisiteFact (obligationId childObligation)) Truth)
      }
  }

childResolved :: ResolvedObligation
childResolved = ResolvedObligation
  { resolvedObligation = childObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = []
  , resolvedDisposition = Phil.Core.Discharge.StaticallyDischarged StaticByDefinition
  }

parentObligation :: Obligation
parentObligation = Obligation
  { obligationId = ObligationId "audit.handoff.parent"
  , obligationProposition = Truth
  , obligationOrigin = "audit"
  , obligationScope = "audit.handoff"
  , obligationRequiredPoint = "manifest-closure"
  }

childObligation :: Obligation
childObligation = Obligation
  { obligationId = ObligationId "audit.handoff.child"
  , obligationProposition = Truth
  , obligationOrigin = "audit"
  , obligationScope = "audit.handoff"
  , obligationRequiredPoint = "manifest-closure"
  }

handoffConfig :: HandoffConfig
handoffConfig = HandoffConfig
  { handoffRevisionKind = const "Audit"
  , handoffRepresentation = const "Core"
  , handoffSubjectIds = const ["subject"]
  , handoffContextIds = const ["context"]
  , handoffAcceptanceRule = \obligation ->
      if obligationId obligation == obligationId parentObligation
        then AcceptEntry KernelChecked (EvidenceRole "certificate")
        else AcceptEntry KernelChecked (EvidenceRole "support")
  }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
