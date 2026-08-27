{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.ProtocolGuard
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError (..))
import Phil.Core.Protocol
import Phil.Core.Session (SessionError (..))
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROT-006 matching branch label does not transfer proof" labelAloneRejects
    , test "PROT-006 exact protocol guard evidence admits transition" exactProtocolGuardAccepts
    , test "PROT-006 evidence for another guard revision does not substitute" wrongGuardRevisionRejects
    , test "PROT-006 architecture strengthening requires its own exact guard" architectureStrengtheningRequiresBoth
    , test "PROT-006 protocol and architecture guards compose conjunctively" bothGuardsAccept
    , test "PROT-006 wrong evidence role does not discharge exact guard" wrongEvidenceRoleRejects
    , test "PROT-006 rejected evidence cannot authorize transition" rejectedEvidenceRejects
    , test "PROT-006 duplicate guard requirements reject" duplicateGuardRejects
    , test "PROT-006 evidence cannot make a structurally illegal label legal" evidenceCannotLegalizeWrongLabel
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

labelAloneRejects :: Either String ()
labelAloneRejects = do
  context <- initialProtocolContext
  let fixture = mkFixture [] []
  case runGuarded fixture protocolOnlyRequest context of
    Left (MissingProtocolTransitionGuardRevision guard) ->
      assert (guard == protocolGuard)
        "label-only rejection named the wrong guard"
    other -> Left ("matching branch label implicitly transferred proof: " <> show other)

exactProtocolGuardAccepts :: Either String ()
exactProtocolGuardAccepts = do
  context <- initialProtocolContext
  let fixture = mkFixture
        [protocolGuardRevisionNode]
        [acceptedEvidence "evidence.protocol.guard" protocolGuardRevisionNode]
  step <- mapLeft show (runGuarded fixture protocolOnlyRequest context)
  successorBinding <- maybe
    (Left "guarded select failed to produce its exact successor")
    Right
    (checkedProtocolSuccessor step)
  assert (protocolEndpointName successorBinding == successor)
    "guarded transition produced the wrong successor occurrence"
  assert (protocolEndpointSession successorBinding == End doneOutcome)
    "guarded transition produced the wrong successor session"

wrongGuardRevisionRejects :: Either String ()
wrongGuardRevisionRejects = do
  context <- initialProtocolContext
  let fixture = mkFixture
        [unrelatedGuardRevisionNode]
        [acceptedEvidence "evidence.unrelated.guard" unrelatedGuardRevisionNode]
  case runGuarded fixture protocolOnlyRequest context of
    Left (MissingProtocolTransitionGuardRevision guard) ->
      assert (guard == protocolGuard)
        "wrong-revision rejection named the wrong required guard"
    other -> Left ("another guard revision substituted for the exact guard: " <> show other)

architectureStrengtheningRequiresBoth :: Either String ()
architectureStrengtheningRequiresBoth = do
  context <- initialProtocolContext
  let fixture = mkFixture
        [protocolGuardRevisionNode]
        [acceptedEvidence "evidence.protocol.guard" protocolGuardRevisionNode]
  case runGuarded fixture strengthenedRequest context of
    Left (MissingProtocolTransitionGuardRevision guard) ->
      assert (guard == architectureGuard)
        "architecture strengthening rejection named the wrong guard"
    other -> Left ("protocol guard silently discharged architecture strengthening: " <> show other)

bothGuardsAccept :: Either String ()
bothGuardsAccept = do
  context <- initialProtocolContext
  let fixture = mkFixture
        [protocolGuardRevisionNode, architectureGuardRevisionNode]
        [ acceptedEvidence "evidence.protocol.guard" protocolGuardRevisionNode
        , acceptedEvidence "evidence.architecture.guard" architectureGuardRevisionNode
        ]
  _ <- mapLeft show (runGuarded fixture strengthenedRequest context)
  pure ()

wrongEvidenceRoleRejects :: Either String ()
wrongEvidenceRoleRejects = do
  context <- initialProtocolContext
  let badEvidence = mkEvidence
        "evidence.protocol.guard.wrong-role"
        protocolGuardRevisionNode
        (EvidenceRole "mentions")
        EvidenceAccepted
      fixture = mkFixture [protocolGuardRevisionNode] [badEvidence]
  case runGuarded fixture protocolOnlyRequest context of
    Left (ProtocolGuardManifestError (AcceptanceRuleUnsatisfied revision)) ->
      assert (revision == revisionId protocolGuardRevisionNode)
        "wrong-role evidence rejection named the wrong obligation"
    other -> Left ("wrong evidence role discharged the exact guard: " <> show other)

rejectedEvidenceRejects :: Either String ()
rejectedEvidenceRejects = do
  context <- initialProtocolContext
  let badEvidence = mkEvidence
        "evidence.protocol.guard.rejected"
        protocolGuardRevisionNode
        guardEvidenceRole
        (EvidenceRejected "guard condition false")
      fixture = mkFixture [protocolGuardRevisionNode] [badEvidence]
  case runGuarded fixture protocolOnlyRequest context of
    Left (ProtocolGuardManifestError (SelectedRejectedEvidence entryId _)) ->
      assert (entryId == evidenceEntryId badEvidence)
        "rejected-evidence diagnostic named the wrong evidence entry"
    other -> Left ("rejected evidence authorized the transition: " <> show other)

duplicateGuardRejects :: Either String ()
duplicateGuardRejects = do
  context <- initialProtocolContext
  let fixture = mkFixture
        [protocolGuardRevisionNode]
        [acceptedEvidence "evidence.protocol.guard" protocolGuardRevisionNode]
      duplicateRequest = GuardedProtocolActionRequest
        { guardedProtocolAction = selectRequest "proceed"
        , guardedProtocolRequirements = [protocolGuard, protocolGuard]
        }
  case runGuarded fixture duplicateRequest context of
    Left (DuplicateProtocolTransitionGuard guard) ->
      assert (guard == protocolGuard)
        "duplicate-guard rejection named the wrong guard"
    other -> Left ("duplicate guard requirements were silently collapsed: " <> show other)

evidenceCannotLegalizeWrongLabel :: Either String ()
evidenceCannotLegalizeWrongLabel = do
  context <- initialProtocolContext
  let fixture = mkFixture
        [protocolGuardRevisionNode]
        [acceptedEvidence "evidence.protocol.guard" protocolGuardRevisionNode]
      request = GuardedProtocolActionRequest
        { guardedProtocolAction = selectRequest "forbidden"
        , guardedProtocolRequirements = [protocolGuard]
        }
  case runGuarded fixture request context of
    Left (ProtocolGuardCoreError (ProtocolSessionError (UnknownSessionLabel label labels))) ->
      assert (label == "forbidden" && labels == ["proceed"])
        "illegal-label rejection lost the structural session diagnostic"
    other -> Left ("guard evidence made an illegal session label legal: " <> show other)

protocolOnlyRequest :: GuardedProtocolActionRequest
protocolOnlyRequest = GuardedProtocolActionRequest
  { guardedProtocolAction = selectRequest "proceed"
  , guardedProtocolRequirements = [protocolGuard]
  }

strengthenedRequest :: GuardedProtocolActionRequest
strengthenedRequest = GuardedProtocolActionRequest
  { guardedProtocolAction = selectRequest "proceed"
  , guardedProtocolRequirements = [protocolGuard, architectureGuard]
  }

selectRequest :: Text -> ProtocolActionRequest
selectRequest label =
  ProtocolSelectRequest endpoint successor protocolInstance clientRole label

protocolGuard :: ProtocolTransitionGuard
protocolGuard = ProtocolTransitionGuard
  { protocolGuardOrigin = ProtocolDeclaredGuard
  , protocolGuardRevision = revisionId protocolGuardRevisionNode
  }

architectureGuard :: ProtocolTransitionGuard
architectureGuard = ProtocolTransitionGuard
  { protocolGuardOrigin = ArchitectureStrengtheningGuard
  , protocolGuardRevision = revisionId architectureGuardRevisionNode
  }

protocolGuardRevisionNode :: ObligationRevision
protocolGuardRevisionNode = guardRevision
  "protocol.transition.guard"
  (Atom "ProtocolAllowsProceed" [])
  "protocol family"

architectureGuardRevisionNode :: ObligationRevision
architectureGuardRevisionNode = guardRevision
  "architecture.transition.guard"
  (Atom "ArchitectureAllowsProceed" [])
  "architecture refinement"

unrelatedGuardRevisionNode :: ObligationRevision
unrelatedGuardRevisionNode = guardRevision
  "protocol.transition.other-guard"
  (Atom "OtherGuard" [])
  "unrelated protocol guard"

guardRevision :: Text -> Proposition -> Text -> ObligationRevision
guardRevision stableId proposition origin = revisionFromCoreObligation
  Obligation
    { obligationId = ObligationId stableId
    , obligationProposition = proposition
    , obligationOrigin = origin
    , obligationScope = "protocol.guard.instance"
    , obligationRequiredPoint = "before select proceed"
    }
  "ProtocolTransitionGuard"
  "Core+Assurance"
  ["protocol.guard.instance", "client", "proceed"]
  []
  (AcceptEntry KernelChecked guardEvidenceRole)
  []

guardEvidenceRole :: EvidenceRole
guardEvidenceRole = EvidenceRole "establishes"

acceptedEvidence :: Text -> ObligationRevision -> EvidenceEntry
acceptedEvidence stableId revision =
  mkEvidence stableId revision guardEvidenceRole EvidenceAccepted

mkEvidence
  :: Text
  -> ObligationRevision
  -> EvidenceRole
  -> EvidenceResult
  -> EvidenceEntry
mkEvidence stableId revision role result = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId stableId
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = KernelChecked
      , evidenceRole = role
      , evidenceProducer = "Phase1ProtocolGuardedTransitionMain"
      , evidenceChecker = "Phil.Assurance.ProtocolGuard / Phil.Assurance.Verify"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = ValidityScope Map.empty
      , evidenceResult = result
      , evidenceJustifies = ["exact transition guard"]
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

data GuardFixture = GuardFixture
  { fixtureVerification :: VerificationContext
  , fixtureLedger :: AssuranceLedger
  , fixtureManifest :: AssuranceManifest
  }

mkFixture :: [ObligationRevision] -> [EvidenceEntry] -> GuardFixture
mkFixture revisions evidence = GuardFixture verification ledger manifest
  where
    revisionMap = Map.fromList [(revisionId revision, revision) | revision <- revisions]
    evidenceMap = Map.fromList [(evidenceEntryId entry, entry) | entry <- evidence]
    revisionSet = Set.fromList (Map.keys revisionMap)
    evidenceSet = Set.fromList (Map.keys evidenceMap)
    ledger = emptyLedger
      { ledgerRevisions = revisionMap
      , ledgerEvidence = evidenceMap
      }
    manifest0 = emptyManifest
      { manifestArchitectureDigest = digestText "phase1.protocol-guard.arch"
      , manifestPhilCoreDigest = digestText "phase1.protocol-guard.core"
      , manifestImplementationDigest = digestText "phase1.protocol-guard.impl"
      , manifestTarget = "host"
      , manifestCompilationProfile = "phase1.protocol-guard"
      , manifestObligationRevisions = revisionSet
      , manifestCertificationScope = revisionSet
      , manifestEvidenceEntries = evidenceSet
      , manifestLoweringLedgerRoot = digestText "phase1.protocol-guard.no-lowering"
      , manifestValidityContext = Map.empty
      }
    manifest = manifest0 { manifestId = deriveManifestId ledger manifest0 }
    verification = emptyVerificationContext
      { verificationArchitectureDigest = manifestArchitectureDigest manifest
      , verificationPhilCoreDigest = manifestPhilCoreDigest manifest
      , verificationImplementationDigest = manifestImplementationDigest manifest
      , verificationTarget = manifestTarget manifest
      , verificationCompilationProfile = manifestCompilationProfile manifest
      , verificationExpectedObligations = revisionSet
      , verificationLoweringLedgerRoot = manifestLoweringLedgerRoot manifest
      , verificationValidityContext = Map.empty
      }

runGuarded
  :: GuardFixture
  -> GuardedProtocolActionRequest
  -> ProtocolContext
  -> Either ProtocolGuardError CheckedProtocolStep
runGuarded fixture request = checkGuardedProtocolAction
  (fixtureVerification fixture)
  (fixtureLedger fixture)
  (fixtureManifest fixture)
  request

initialProtocolContext :: Either String ProtocolContext
initialProtocolContext = mapLeft show $
  insertProtocolEndpoint endpoint protocolInstance clientRole initialSession emptyProtocolContext

initialSession :: Session
initialSession = Select
  [ Branch
      { branchLabel = "proceed"
      , branchPayload = Nothing
      , branchContinuation = End doneOutcome
      }
  ]

protocolInstance :: ProtocolInstanceRevision
protocolInstance = ProtocolInstanceRevision "protocol.guarded.instance:v1"

clientRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "client"

endpoint, successor :: Name
endpoint = Name "endpoint.guarded.0"
successor = Name "endpoint.guarded.1"

doneOutcome :: Outcome
doneOutcome = Outcome "done"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
