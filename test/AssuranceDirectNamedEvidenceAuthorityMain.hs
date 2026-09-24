{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.EvidenceFactAuthority
  ( EvidenceFactAuthorityError (..)
  , handoffResolvedObligationWithAllEvidenceAuthority
  )
import Phil.Assurance.Handoff
  ( DirectEvidenceAuthorityBinding (..)
  , HandoffConfig (..)
  , HandoffError (..)
  , LedgerHandoff (..)
  , bindHandoffDirectEvidence
  , handoffResolvedObligation
  , handoffSupportEdges
  )
import Phil.Assurance.Types
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
  , RefTerm (..)
  )
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , VerificationObligationGraph (..)
  , buildVerificationRevisionGraphWithSupport
  )
import qualified Phil.Verification as Verification
import Phil.Verification.Bundle
  ( VerificationBundle
  , buildVerificationBundle
  , verificationBundleArchitectureDigest
  )
import Phil.Verification.ManifestClosure
import System.Exit (exitFailure)

data Fixture = Fixture
  { fixtureGraph :: VerificationObligationGraph
  , fixtureBundle :: VerificationBundle
  , fixturePolicy :: ApplicationAssurancePolicy
  , fixtureContext :: VerificationContext
  , fixtureLedger :: AssuranceLedger
  , fixtureSelection :: ManifestClosureSelection
  , fixtureHandoff :: ManifestClosureHandoff
  , fixtureConsumerRevision :: RevisionId
  , fixtureConsumerEvidenceId :: EvidenceEntryId
  , fixtureSourceEvidenceId :: EvidenceEntryId
  }

main :: IO ()
main = do
  results <- sequence
    [ test "direct named evidence closes with exact immutable authority" happyPath
    , test "raw direct handoff without immutable support is rejected" rawDirectSupportRejected
    , test "direct name requires an exact checking-event authority binding" missingEventAuthorityRejected
    , test "same-spelled authority with wrong proposition is rejected" wrongPropositionRejected
    , test "same-spelled authority with wrong subject identity is rejected" wrongSubjectRejected
    , test "same-spelled authority with wrong scope is rejected" wrongScopeRejected
    , test "final closure requires a binding for every direct handoff" missingDirectClosureBindingRejected
    , test "final closure rejects direct evidence that drops its selected proof" droppedDirectSupportRejected
    , test "final closure rejects a direct binding to another evidence revision" wrongDirectClosureEvidenceRejected
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

rawDirectSupportRejected :: Either String ()
rawDirectSupportRejected = do
  entries <- mapLeft show (handoffResolvedObligation handoffConfig directResolved)
  entry <- one entries
  let revision = revisionId (handoffRevision entry)
  case bindHandoffDirectEvidence entry (mkConsumerEvidence revision) of
    Left (HandoffDirectEvidenceSupportMissing actual name')
      | actual == revision
      , name' == proofName -> Right ()
    other -> Left ("expected missing direct support, got " <> show other)

missingEventAuthorityRejected :: Either String ()
missingEventAuthorityRejected = do
  let (revision, evidence) = sourcePair
      ledger = sourceLedger revision evidence
      wrongEvent = ObligationId "audit.direct.other-event"
      authorities = Map.singleton
        (wrongEvent, proofName)
        (DirectEvidenceAuthorityBinding sourceEvidenceId)
      expected = EvidenceFactAuthorityHandoffError
        (MissingDirectEvidenceAuthority consumerId proofName)
  case handoffResolvedObligationWithAllEvidenceAuthority
      handoffConfig Map.empty authorities ledger directResolved of
    Left err | err == expected -> Right ()
    other -> Left ("expected exact-event authority rejection, got " <> show other)

wrongPropositionRejected :: Either String ()
wrongPropositionRejected = do
  let revision = sourceRevision "wrong-proposition" Falsehood [subjectId] consumerScope
      evidence = sealEvidence (mkSourceEvidence sourceEvidenceId revision)
  expectAuthorityFailure
    (sourceLedger revision evidence)
    (DirectEvidenceAuthorityPropositionMismatch consumerId proofName
      (renderPropositionCanonical directProposition)
      (revisionStatement revision))

wrongSubjectRejected :: Either String ()
wrongSubjectRejected = do
  let revision = sourceRevision "wrong-subject" directProposition ["subject.other"] consumerScope
      evidence = sealEvidence (mkSourceEvidence sourceEvidenceId revision)
  expectAuthorityFailure
    (sourceLedger revision evidence)
    (DirectEvidenceAuthoritySubjectMismatch consumerId proofName
      [subjectId] ["subject.other"])

wrongScopeRejected :: Either String ()
wrongScopeRejected = do
  let revision = sourceRevision "wrong-scope" directProposition [subjectId] "audit.other-scope"
      evidence = sealEvidence (mkSourceEvidence sourceEvidenceId revision)
  expectAuthorityFailure
    (sourceLedger revision evidence)
    (DirectEvidenceAuthorityScopeMismatch consumerId proofName
      consumerScope "audit.other-scope")

missingDirectClosureBindingRejected :: Either String ()
missingDirectClosureBindingRejected = do
  fixture <- baseFixture
  let handoff = (fixtureHandoff fixture)
        { manifestClosureDirectEvidence = Map.empty }
      changed = fixture { fixtureHandoff = handoff }
      expected = Set.singleton (fixtureConsumerRevision fixture)
  case closeFixture changed of
    Left (ManifestClosureHandoffDirectEvidenceDomainMismatch actual supplied)
      | actual == expected
      , Set.null supplied -> Right ()
    other -> Left ("expected direct evidence-domain mismatch, got " <> show other)

droppedDirectSupportRejected :: Either String ()
droppedDirectSupportRejected = do
  fixture <- baseFixture
  consumer <- consumerEvidence fixture
  let mutated = sealEvidence consumer { evidenceDependsOn = [] }
  changed <- rebuildConsumerEvidence fixture mutated
  case closeFixture changed of
    Left (ManifestClosureHandoffEvidenceMismatch revision entryId)
      | revision == fixtureConsumerRevision fixture
      , entryId == fixtureConsumerEvidenceId fixture -> Right ()
    other -> Left ("expected direct handoff evidence mismatch, got " <> show other)

wrongDirectClosureEvidenceRejected :: Either String ()
wrongDirectClosureEvidenceRejected = do
  fixture <- baseFixture
  let handoff = (fixtureHandoff fixture)
        { manifestClosureDirectEvidence = Map.singleton
            (fixtureConsumerRevision fixture)
            (fixtureSourceEvidenceId fixture)
        }
      changed = fixture { fixtureHandoff = handoff }
  case closeFixture changed of
    Left (ManifestClosureHandoffEvidenceRejected revision entryId
        (HandoffEvidenceRevisionMismatch expected actual))
      | revision == fixtureConsumerRevision fixture
      , entryId == fixtureSourceEvidenceId fixture
      , expected == fixtureConsumerRevision fixture
      , actual /= expected -> Right ()
    other -> Left ("expected direct revision mismatch, got " <> show other)

expectAuthorityFailure :: AssuranceLedger -> HandoffError -> Either String ()
expectAuthorityFailure ledger expectedHandoff =
  let expected = EvidenceFactAuthorityHandoffError expectedHandoff
  in case handoffResolvedObligationWithAllEvidenceAuthority
      handoffConfig Map.empty directAuthorities ledger directResolved of
    Left err | err == expected -> Right ()
    other -> Left ("expected authority failure " <> show expected <> ", got " <> show other)

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
  let (sourceRevisionValue, sourceEvidenceValue) = sourcePair
      initialLedger = sourceLedger sourceRevisionValue sourceEvidenceValue
  entries <- mapLeft show $ handoffResolvedObligationWithAllEvidenceAuthority
    handoffConfig Map.empty directAuthorities initialLedger directResolved
  entry <- one entries
  let consumerRevisionValue = handoffRevision entry
      consumerRevisionId = revisionId consumerRevisionValue
      scope = Set.fromList [consumerRevisionId, revisionId sourceRevisionValue]
  graph <- mapLeft show $ buildVerificationRevisionGraphWithSupport
    [consumerRevisionValue, sourceRevisionValue]
    (handoffSupportEdges entries)
    scope
  consumerEvidenceValue <- mapLeft show $
    bindHandoffDirectEvidence entry (mkConsumerEvidence consumerRevisionId)
  let policy = ApplicationAssurancePolicy
        { applicationAssurancePolicyRevision = AssurancePolicyRevision
            "audit-direct-evidence-v1"
        , applicationAssurancePolicyPermittedDispositions =
            Set.singleton Verification.StaticallyDischarged
        }
  bundle <- mapLeft show $ buildVerificationBundle
    (digestText "audit-direct-evidence-source")
    [] [] []
    graph
    policy
    [consumerEvidenceValue, sourceEvidenceValue]
  let ledger = emptyLedger
        { ledgerRevisions = verificationGraphNodes graph
        , ledgerEvidence = Map.fromList
            [ (consumerEvidenceId, consumerEvidenceValue)
            , (sourceEvidenceId, sourceEvidenceValue)
            ]
        }
      context = emptyVerificationContext
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationPhilCoreDigest = digestText "audit-direct-evidence-core"
        , verificationImplementationDigest = digestText "audit-direct-evidence-impl"
        , verificationTarget = "audit-direct-evidence-target"
        , verificationCompilationProfile = "checked-runtime"
        , verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        , verificationLoweringLedgerRoot = digestText "audit-direct-evidence-lowering"
        }
      selection = ManifestClosureSelection
        { manifestClosureEvidence = Set.fromList [consumerEvidenceId, sourceEvidenceId]
        , manifestClosureAssumptions = Set.empty
        , manifestClosureExports = Map.empty
        , manifestClosureUses = Set.empty
        }
      handoff = ManifestClosureHandoff
        { manifestClosureHandoffEntries = entries
        , manifestClosureCertificateEvidence = Map.empty
        , manifestClosureDirectEvidence = Map.singleton
            consumerRevisionId consumerEvidenceId
        }
  Right Fixture
    { fixtureGraph = graph
    , fixtureBundle = bundle
    , fixturePolicy = policy
    , fixtureContext = context
    , fixtureLedger = ledger
    , fixtureSelection = selection
    , fixtureHandoff = handoff
    , fixtureConsumerRevision = consumerRevisionId
    , fixtureConsumerEvidenceId = consumerEvidenceId
    , fixtureSourceEvidenceId = sourceEvidenceId
    }

rebuildConsumerEvidence :: Fixture -> EvidenceEntry -> Either String Fixture
rebuildConsumerEvidence fixture replacement = do
  source <- sourceEvidence fixture
  bundle <- mapLeft show $ buildVerificationBundle
    (digestText "audit-direct-evidence-source")
    [] [] []
    (fixtureGraph fixture)
    (fixturePolicy fixture)
    [replacement, source]
  let ledger0 = fixtureLedger fixture
      ledger = ledger0
        { ledgerEvidence = Map.insert
            (fixtureConsumerEvidenceId fixture)
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

consumerEvidence :: Fixture -> Either String EvidenceEntry
consumerEvidence fixture =
  case Map.lookup (fixtureConsumerEvidenceId fixture)
      (ledgerEvidence (fixtureLedger fixture)) of
    Nothing -> Left "consumer evidence missing"
    Just value -> Right value

sourceEvidence :: Fixture -> Either String EvidenceEntry
sourceEvidence fixture =
  case Map.lookup (fixtureSourceEvidenceId fixture)
      (ledgerEvidence (fixtureLedger fixture)) of
    Nothing -> Left "source evidence missing"
    Just value -> Right value

sourcePair :: (ObligationRevision, EvidenceEntry)
sourcePair =
  let revision = sourceRevision "proof" directProposition [subjectId] consumerScope
  in (revision, sealEvidence (mkSourceEvidence sourceEvidenceId revision))

sourceLedger :: ObligationRevision -> EvidenceEntry -> AssuranceLedger
sourceLedger revision evidence = emptyLedger
  { ledgerRevisions = Map.singleton (revisionId revision) revision
  , ledgerEvidence = Map.singleton (evidenceEntryId evidence) evidence
  }

sourceRevision :: Text -> Proposition -> [Text] -> Text -> ObligationRevision
sourceRevision suffix proposition subjects scope =
  revisionFromCoreObligation
    Obligation
      { obligationId = ObligationId ("audit.direct.source." <> suffix)
      , obligationProposition = proposition
      , obligationOrigin = "audit"
      , obligationScope = scope
      , obligationRequiredPoint = "proof-establishment"
      }
    "Audit"
    "Core"
    subjects
    ["context.audit.direct"]
    (AcceptEntry KernelChecked (EvidenceRole "direct-proof"))
    []

mkSourceEvidence :: EvidenceEntryId -> ObligationRevision -> EvidenceEntry
mkSourceEvidence entryId revision = EvidenceEntry
  { evidenceEntryId = entryId
  , evidenceEntryDigest = Digest ""
  , evidenceObligationRevision = revisionId revision
  , evidenceAssuranceKind = KernelChecked
  , evidenceRole = EvidenceRole "direct-proof"
  , evidenceProducer = "authoritative direct proof registry"
  , evidenceChecker = "Phil Core"
  , evidenceArtifact = Nothing
  , evidenceInputDigests = []
  , evidenceAssumptions = []
  , evidenceDependsOn = []
  , evidenceValidityScope = ValidityScope Map.empty
  , evidenceResult = EvidenceAccepted
  , evidenceJustifies = ["exact named proof proposition"]
  , evidenceRuntimeMechanism = Nothing
  , evidenceRuntimeResidue = []
  , evidenceCostRefs = []
  }

mkConsumerEvidence :: RevisionId -> EvidenceEntry
mkConsumerEvidence revision = EvidenceEntry
  { evidenceEntryId = consumerEvidenceId
  , evidenceEntryDigest = Digest "unbound-before-handoff"
  , evidenceObligationRevision = revision
  , evidenceAssuranceKind = KernelChecked
  , evidenceRole = EvidenceRole "direct-discharge"
  , evidenceProducer = "Phil Core direct evidence resolver"
  , evidenceChecker = "Phil Core"
  , evidenceArtifact = Nothing
  , evidenceInputDigests = []
  , evidenceAssumptions = []
  , evidenceDependsOn = []
  , evidenceValidityScope = ValidityScope Map.empty
  , evidenceResult = EvidenceAccepted
  , evidenceJustifies = ["direct named evidence"]
  , evidenceRuntimeMechanism = Nothing
  , evidenceRuntimeResidue = []
  , evidenceCostRefs = []
  }

sealEvidence :: EvidenceEntry -> EvidenceEntry
sealEvidence entry = entry { evidenceEntryDigest = deriveEvidenceEntryDigest entry }

one :: [a] -> Either String a
one values = case values of
  [value] -> Right value
  _ -> Left ("expected exactly one handoff entry, got " <> show (length values))

directAuthorities :: Map.Map (ObligationId, Name) DirectEvidenceAuthorityBinding
directAuthorities = Map.singleton
  (consumerId, proofName)
  (DirectEvidenceAuthorityBinding sourceEvidenceId)

handoffConfig :: HandoffConfig
handoffConfig = HandoffConfig
  { handoffRevisionKind = const "Audit"
  , handoffRepresentation = const "Core"
  , handoffSubjectIds = const [subjectId]
  , handoffContextIds = const ["context.audit.direct"]
  , handoffAcceptanceRule = const
      (AcceptEntry KernelChecked (EvidenceRole "direct-discharge"))
  }

directResolved :: ResolvedObligation
directResolved = ResolvedObligation
  { resolvedObligation = consumerObligation
  , resolvedCanonicalProposition = directProposition
  , resolvedPrerequisites = []
  , resolvedDisposition = StaticallyDischarged (StaticByEvidence proofName)
  }

consumerObligation :: Obligation
consumerObligation = Obligation
  { obligationId = consumerId
  , obligationProposition = directProposition
  , obligationOrigin = "audit"
  , obligationScope = consumerScope
  , obligationRequiredPoint = "manifest-closure"
  }

consumerId :: ObligationId
consumerId = ObligationId "audit.direct.consumer"

proofName :: Name
proofName = Name "proof"

directProposition :: Proposition
directProposition = Atom "DirectClaim" [RefVar (Name "payload")]

subjectId :: Text
subjectId = "subject.payload"

consumerScope :: Text
consumerScope = "audit.direct.scope"

sourceEvidenceId :: EvidenceEntryId
sourceEvidenceId = EvidenceEntryId "evidence.audit.direct.source"

consumerEvidenceId :: EvidenceEntryId
consumerEvidenceId = EvidenceEntryId "evidence.audit.direct.consumer"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
