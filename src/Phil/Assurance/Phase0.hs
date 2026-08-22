{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.Phase0
  ( phase0UploadLedger
  , phase0UploadManifest
  , phase0UploadVerificationContext
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

phase0UploadLedger :: AssuranceLedger
phase0UploadLedger = emptyLedger
  { ledgerRevisions = Map.fromList [(revisionId revision, revision) | revision <- revisions]
  , ledgerEvidence = Map.fromList [(evidenceEntryId entry, entry) | entry <- evidenceEntries]
  , ledgerAssumptions = Map.fromList [(assumptionId assumption, assumption) | assumption <- assumptions]
  , ledgerUses = Map.fromList [(assuranceUseId use, use) | use <- assuranceUses]
  }

phase0UploadManifest :: AssuranceManifest
phase0UploadManifest = provisionalManifest
  { manifestId = deriveManifestId phase0UploadLedger provisionalManifest }

phase0UploadVerificationContext :: VerificationContext
phase0UploadVerificationContext = emptyVerificationContext
  { verificationArchitectureDigest = architectureDigest
  , verificationPhilCoreDigest = coreDigest
  , verificationImplementationDigest = implementationDigest
  , verificationTarget = "phase0-semantic"
  , verificationCompilationProfile = "semantic/reference"
  , verificationExpectedObligations = Set.fromList (map revisionId revisions)
  , verificationPermittedAssumptions = Set.fromList (map assumptionId assumptions)
  , verificationLoweringLedgerRoot = loweringRoot
  , verificationKnownCostRefs = Set.fromList runtimeCostRefs
  , verificationValidityContext = validityContext
  }

provisionalManifest :: AssuranceManifest
provisionalManifest = emptyManifest
  { manifestArchitectureDigest = architectureDigest
  , manifestPhilCoreDigest = coreDigest
  , manifestImplementationDigest = implementationDigest
  , manifestTarget = "phase0-semantic"
  , manifestCompilationProfile = "semantic/reference"
  , manifestObligationRevisions = revisionSet
  , manifestCertificationScope = revisionSet
  , manifestEvidenceEntries = Set.fromList (map evidenceEntryId evidenceEntries)
  , manifestAssumptionNodes = Set.fromList (map assumptionId assumptions)
  , manifestAssuranceUses = Set.fromList (map assuranceUseId assuranceUses)
  , manifestLoweringLedgerRoot = loweringRoot
  , manifestValidityContext = validityContext
  }
  where
    revisionSet = Set.fromList (map revisionId revisions)

architectureDigest :: Digest
architectureDigest = digestText "Phil Phase 0 Upload demonstrator accepted architecture"

coreDigest :: Digest
coreDigest = digestText "Phil Core semantic/reference checker boundary"

implementationDigest :: Digest
implementationDigest = digestText "Phil Phase 0 upload semantic/reference implementation"

loweringRoot :: Digest
loweringRoot = digestText "upload-runtime-cost-plan.md semantic/reference root"

validityContext :: Map.Map Text Text
validityContext = Map.fromList
  [ ("architecture", "Upload demonstrator")
  , ("roles", "Client,Server")
  , ("transport", "synchronous ordered Phase 0 model")
  ]

runtimeScope :: ValidityScope
runtimeScope = ValidityScope validityContext

unscoped :: ValidityScope
unscoped = ValidityScope Map.empty

role :: Text -> EvidenceRole
role = EvidenceRole

allOf :: [(AssuranceKind, Text)] -> AcceptanceRule
allOf = AcceptAll . map (uncurry entryRule)

entryRule :: AssuranceKind -> Text -> AcceptanceRule
entryRule kind roleName = AcceptEntry kind (role roleName)

mkRevision :: Text -> Text -> AcceptanceRule -> ObligationRevision
mkRevision obligationName statement acceptance = provisional
  { revisionId = deriveRevisionId provisional }
  where
    provisional = ObligationRevision
      { revisionObligationId = ObligationId obligationName
      , revisionId = RevisionId ""
      , revisionStatement = statement
      , revisionStatementDigest = digestText statement
      , revisionKind = "Phase0Upload"
      , revisionOrigin = "docs/semantics/upload-assurance-ledger.md"
      , revisionScope = "upload.phase0.reference"
      , revisionRequiredAt = "certification"
      , revisionRepresentation = "surface/Core semantic witness"
      , revisionSubjectIds = []
      , revisionContextIds = []
      , revisionAcceptanceRule = acceptance
      , revisionGeneratedFrom = []
      }

helloIngress :: ObligationRevision
helloIngress = mkRevision
  "upload.ingress.hello.complete_recognition"
  "Hello semantic continuation exists only after the complete frame is recognized as Hello"
  (allOf [(KernelChecked, "establishes"), (RuntimeEnforced, "runtime_enforces")])

beginIngress :: ObligationRevision
beginIngress = mkRevision
  "upload.ingress.begin.complete_recognition"
  "Begin semantic continuation exists only after the complete frame is recognized as Begin"
  (allOf [(KernelChecked, "establishes"), (RuntimeEnforced, "runtime_enforces")])

helloPolicy :: ObligationRevision
helloPolicy = mkRevision
  "upload.hello.policy"
  "HelloPolicy(kappa, hello)"
  (allOf [(KernelChecked, "checks_evidence_identity"), (RuntimeEnforced, "runtime_enforces")])

versionServer :: ObligationRevision
versionServer = mkRevision
  "upload.version.offered.server_selection"
  "member(selected, hello.versions) at Server selection"
  (entryRule KernelChecked "establishes")

versionClient :: ObligationRevision
versionClient = mkRevision
  "upload.version.offered.client_receive"
  "member(selected, hello.versions) at Client receive"
  (entryRule RuntimeEnforced "boundary_establishes")

unsupportedDisjoint :: ObligationRevision
unsupportedDisjoint = mkRevision
  "upload.version.unsupported_disjoint"
  "disjoint(serverSupported, hello.versions)"
  (entryRule KernelChecked "establishes")

beginPolicy :: ObligationRevision
beginPolicy = mkRevision
  "upload.begin.policy"
  "BeginPolicy(kappa, begin)"
  (allOf [(KernelChecked, "checks_evidence_identity"), (RuntimeEnforced, "runtime_enforces")])

payloadExactReceive :: ObligationRevision
payloadExactReceive = mkRevision
  "upload.payload.exact_length"
  "received body has exactly toNat(begin.length) bytes"
  (allOf [(KernelChecked, "establishes_result_type"), (RuntimeEnforced, "runtime_enforces")])

payloadExactSend :: ObligationRevision
payloadExactSend = mkRevision
  "upload.payload.exact_length.client_send"
  "payload branch sends exactly toNat(begin.length) bytes"
  (allOf [(KernelChecked, "checks_message_index"), (RuntimeEnforced, "runtime_transfer")])

digestMatches :: ObligationRevision
digestMatches = mkRevision
  "upload.digest.matches"
  "DigestMatches(begin, payload_id)"
  (allOf [(KernelChecked, "checks_evidence_identity"), (RuntimeEnforced, "runtime_enforces")])

storageSuccess :: ObligationRevision
storageSuccess = mkRevision
  "upload.accepted.storage_success"
  "accepted(id) is selected only after store(payload) succeeded and produced id"
  (allOf [(KernelChecked, "control_flow"), (RuntimeEnforced, "runtime_operation")])

revisions :: [ObligationRevision]
revisions =
  [ helloIngress
  , beginIngress
  , helloPolicy
  , versionServer
  , versionClient
  , unsupportedDisjoint
  , beginPolicy
  , payloadExactReceive
  , payloadExactSend
  , digestMatches
  , storageSuccess
  ]

mkAssumption :: Text -> Text -> Text -> Assumption
mkAssumption stableId statement owner = provisional
  { assumptionDigest = deriveAssumptionDigest provisional }
  where
    provisional = Assumption
      { assumptionId = AssumptionId stableId
      , assumptionDigest = Digest ""
      , assumptionStatement = statement
      , assumptionScope = "upload.phase0.reference"
      , assumptionOwnerBoundary = owner
      , assumptionRationale = "Residual Phase 0 runtime trust boundary from the normative upload assurance witness"
      , assumptionValidityScope = runtimeScope
      }

receiveExactAssumption :: Assumption
receiveExactAssumption = mkAssumption
  "assumption.runtime.receive_exact_contract"
  "runtime receive_exact obeys its declared success/failure and cleanup contract"
  "runtime primitives / TCB"

frameReceiveAssumption :: Assumption
frameReceiveAssumption = mkAssumption
  "assumption.runtime.frame_receive_contract"
  "runtime frame acquisition preserves complete-frame bytes and PendingRecv lifecycle as declared"
  "runtime primitives / TCB"

digestImplementationAssumption :: Assumption
digestImplementationAssumption = mkAssumption
  "assumption.runtime.digest_implementation"
  "configured digest implementation realizes the declared SHA-256 semantics for the bytes presented to it"
  "crypto/runtime implementation"

storageContractAssumption :: Assumption
storageContractAssumption = mkAssumption
  "assumption.runtime.storage_contract"
  "store consumes/releases OwnedBytes on both success and failure and returns UploadId only on successful storage"
  "storage primitive / runtime"

assumptions :: [Assumption]
assumptions =
  [ receiveExactAssumption
  , frameReceiveAssumption
  , digestImplementationAssumption
  , storageContractAssumption
  ]

mkEvidence
  :: Text
  -> ObligationRevision
  -> AssuranceKind
  -> Text
  -> Text
  -> Text
  -> [AssumptionId]
  -> [EvidenceDependency]
  -> Maybe RuntimeMechanism
  -> [Text]
  -> [Text]
  -> EvidenceEntry
mkEvidence stableId revision kind roleName producer checker assumptionIds dependencies runtimeMechanism residue costRefs =
  provisional { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId stableId
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = kind
      , evidenceRole = role roleName
      , evidenceProducer = producer
      , evidenceChecker = checker
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = assumptionIds
      , evidenceDependsOn = dependencies
      , evidenceValidityScope = if kind == RuntimeEnforced then runtimeScope else unscoped
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = []
      , evidenceRuntimeMechanism = runtimeMechanism
      , evidenceRuntimeResidue = residue
      , evidenceCostRefs = costRefs
      }

runtime
  :: Text
  -> Text
  -> Text
  -> Text
  -> RuntimeMechanism
runtime name point success failure = RuntimeMechanism
  { runtimeMechanismName = name
  , runtimeExecutionPoint = point
  , runtimeSuccessEvidenceType = success
  , runtimeFailureContract = failure
  , runtimeImplementation = Nothing
  }

helloIngressKernel :: EvidenceEntry
helloIngressKernel = mkEvidence
  "evidence.upload.ingress.hello.kernel"
  helloIngress KernelChecked "establishes"
  "Phil Core recognition checker" "Phil Core"
  [] [] Nothing [] []

helloIngressRuntime :: EvidenceEntry
helloIngressRuntime = mkEvidence
  "evidence.upload.ingress.hello.runtime"
  helloIngress RuntimeEnforced "runtime_enforces"
  "receive_frame + Hello recognizer + commit_receive" "declared ingress boundary"
  [assumptionId frameReceiveAssumption] []
  (Just (runtime
    "Hello frame recognition boundary"
    "server Hello ingress"
    "Parsed[Hello, frame_id, hello] plus successor Endpoint"
    "recognition failure fatally consumes PendingRecv and creates no successor"))
  ["frame acquisition, recognition, and commit"]
  ["upload.runtime.frame_receive"]

beginIngressKernel :: EvidenceEntry
beginIngressKernel = mkEvidence
  "evidence.upload.ingress.begin.kernel"
  beginIngress KernelChecked "establishes"
  "Phil Core recognition checker" "Phil Core"
  [] [] Nothing [] []

beginIngressRuntime :: EvidenceEntry
beginIngressRuntime = mkEvidence
  "evidence.upload.ingress.begin.runtime"
  beginIngress RuntimeEnforced "runtime_enforces"
  "receive_frame + Begin recognizer + commit_receive" "declared ingress boundary"
  [assumptionId frameReceiveAssumption] []
  (Just (runtime
    "Begin frame recognition boundary"
    "server Begin ingress"
    "Parsed[Begin, frame_id, begin] plus successor Endpoint"
    "recognition failure fatally consumes PendingRecv and creates no successor"))
  ["frame acquisition, recognition, and commit"]
  ["upload.runtime.frame_receive"]

helloPolicyKernel :: EvidenceEntry
helloPolicyKernel = mkEvidence
  "evidence.upload.hello_policy.kernel"
  helloPolicy KernelChecked "checks_evidence_identity"
  "Phil surface/Core checker" "Phil Core"
  [] [] Nothing [] []

helloPolicyRuntime :: EvidenceEntry
helloPolicyRuntime = mkEvidence
  "evidence.upload.hello_policy.runtime"
  helloPolicy RuntimeEnforced "runtime_enforces"
  "HelloPolicy validator" "declared validator boundary"
  [] []
  (Just (runtime
    "HelloPolicy validator"
    "after Hello recognition, before version selection"
    "Validated[HelloPolicy, kappa, hello]"
    "validation failure is fatal in the frozen protocol"))
  ["HelloPolicy evaluation"]
  ["upload.runtime.hello_policy"]

versionServerKernel :: EvidenceEntry
versionServerKernel = mkEvidence
  "evidence.upload.version.server.kernel"
  versionServer KernelChecked "establishes"
  "choose_supported primitive contract" "Phil Core"
  [] [] Nothing [] []

versionClientRuntime :: EvidenceEntry
versionClientRuntime = mkEvidence
  "evidence.upload.version.client.runtime"
  versionClient RuntimeEnforced "boundary_establishes"
  "refined branch-message boundary adapter" "declared session boundary"
  [] []
  (Just (runtime
    "version branch refinement adapter"
    "Client version branch receive"
    "selected : {v : U16 | member(v, hello.versions)}"
    "branch decode/validation failure does not bind selected"))
  ["branch payload refinement check"]
  ["upload.runtime.branch_refinement"]

unsupportedKernel :: EvidenceEntry
unsupportedKernel = mkEvidence
  "evidence.upload.version.unsupported.kernel"
  unsupportedDisjoint KernelChecked "establishes"
  "choose_supported primitive contract" "Phil Core"
  [] [] Nothing [] []

beginPolicyKernel :: EvidenceEntry
beginPolicyKernel = mkEvidence
  "evidence.upload.begin_policy.kernel"
  beginPolicy KernelChecked "checks_evidence_identity"
  "Phil surface/Core checker" "Phil Core"
  [] [] Nothing [] []

beginPolicyRuntime :: EvidenceEntry
beginPolicyRuntime = mkEvidence
  "evidence.upload.begin_policy.runtime"
  beginPolicy RuntimeEnforced "runtime_enforces"
  "BeginPolicy validator" "declared validator boundary"
  [] []
  (Just (runtime
    "BeginPolicy validator"
    "after Begin recognition, before proceed/reject"
    "Validated[BeginPolicy, kappa, begin]"
    "validation failure selects reject(reason)"))
  ["BeginPolicy evaluation"]
  ["upload.runtime.begin_policy"]

receiveContractEvidence :: EvidenceEntry
receiveContractEvidence = mkEvidence
  "evidence.upload.payload.receive_contract.kernel"
  payloadExactReceive KernelChecked "primitive_contract"
  "receive_exact primitive declaration" "Phil Core"
  [] [] Nothing [] []

payloadReceiveKernel :: EvidenceEntry
payloadReceiveKernel = mkEvidence
  "evidence.upload.payload.receive.kernel"
  payloadExactReceive KernelChecked "establishes_result_type"
  "receive_exact dependent result type" "Phil Core"
  [] [DependsOnEvidence (evidenceEntryId receiveContractEvidence)] Nothing [] []

payloadReceiveRuntime :: EvidenceEntry
payloadReceiveRuntime = mkEvidence
  "evidence.upload.payload.receive.runtime"
  payloadExactReceive RuntimeEnforced "runtime_enforces"
  "receive_exact" "declared runtime primitive boundary"
  [assumptionId receiveExactAssumption] []
  (Just (runtime
    "receive_exact"
    "Server payload receive"
    "OwnedBytes[toNat(begin.length)]"
    "EarlyEOF consumes endpoint, releases partial buffer, returns no OwnedBytes[n]"))
  ["exact receive / early-EOF check"]
  ["upload.runtime.receive_exact"]

payloadSendKernel :: EvidenceEntry
payloadSendKernel = mkEvidence
  "evidence.upload.payload.send.kernel"
  payloadExactSend KernelChecked "checks_message_index"
  "Phil session/value checker" "Phil Core"
  [] [] Nothing [] []

payloadSendRuntime :: EvidenceEntry
payloadSendRuntime = mkEvidence
  "evidence.upload.payload.send.runtime"
  payloadExactSend RuntimeEnforced "runtime_transfer"
  "send_exact" "declared transport boundary"
  [] []
  (Just (runtime
    "send_exact"
    "Client payload send"
    "successful transfer of Bytes[toNat(begin.length)]"
    "transport failure produces no successful payload continuation"))
  ["exact byte transfer / transport failure handling"]
  ["upload.runtime.send_exact"]

digestKernel :: EvidenceEntry
digestKernel = mkEvidence
  "evidence.upload.digest.kernel"
  digestMatches KernelChecked "checks_evidence_identity"
  "Phil selection/evidence checker" "Phil Core"
  [] [] Nothing [] []

digestRuntime :: EvidenceEntry
digestRuntime = mkEvidence
  "evidence.upload.digest.runtime"
  digestMatches RuntimeEnforced "runtime_enforces"
  "digest validator" "declared digest-validator boundary"
  [assumptionId digestImplementationAssumption] []
  (Just (runtime
    "SHA-256 digest validator"
    "after payload receive, before accepted/rejected"
    "Proof[DigestMatches(begin, payload_id)]"
    "DigestFailure leaves payload owner available for release/rejected path"))
  ["SHA-256 computation and comparison"]
  ["upload.runtime.digest"]

storageKernel :: EvidenceEntry
storageKernel = mkEvidence
  "evidence.upload.storage.kernel"
  storageSuccess KernelChecked "control_flow"
  "Phil process/session checker" "Phil Core"
  [] [DependsOnObligation (revisionId digestMatches)] Nothing [] []

storageRuntime :: EvidenceEntry
storageRuntime = mkEvidence
  "evidence.upload.storage.runtime"
  storageSuccess RuntimeEnforced "runtime_operation"
  "store" "declared storage primitive boundary"
  [assumptionId storageContractAssumption]
  [DependsOnObligation (revisionId digestMatches)]
  (Just (runtime
    "store"
    "after digest validation, before accepted(id)"
    "UploadId on successful storage"
    "storage failure consumes/releases payload and produces no accepted branch"))
  ["payload storage operation"]
  ["upload.runtime.store"]

evidenceEntries :: [EvidenceEntry]
evidenceEntries =
  [ helloIngressKernel
  , helloIngressRuntime
  , beginIngressKernel
  , beginIngressRuntime
  , helloPolicyKernel
  , helloPolicyRuntime
  , versionServerKernel
  , versionClientRuntime
  , unsupportedKernel
  , beginPolicyKernel
  , beginPolicyRuntime
  , receiveContractEvidence
  , payloadReceiveKernel
  , payloadReceiveRuntime
  , payloadSendKernel
  , payloadSendRuntime
  , digestKernel
  , digestRuntime
  , storageKernel
  , storageRuntime
  ]

runtimeCostRefs :: [Text]
runtimeCostRefs =
  [ "upload.runtime.frame_receive"
  , "upload.runtime.hello_policy"
  , "upload.runtime.branch_refinement"
  , "upload.runtime.begin_policy"
  , "upload.runtime.receive_exact"
  , "upload.runtime.send_exact"
  , "upload.runtime.digest"
  , "upload.runtime.store"
  ]

mkRuntimeUse :: Text -> ObligationRevision -> EvidenceEntry -> Text -> AssuranceUse
mkRuntimeUse stableId revision entry costRef = provisional
  { assuranceUseDigest = deriveAssuranceUseDigest provisional }
  where
    provisional = RetainedRuntimeUse
      { assuranceUseId = AssuranceUseId stableId
      , assuranceUseDigest = Digest ""
      , useObligationRevision = revisionId revision
      , useRuntimeEvidence = evidenceEntryId entry
      , useCostRef = costRef
      }

assuranceUses :: [AssuranceUse]
assuranceUses =
  [ mkRuntimeUse "use.upload.hello_ingress" helloIngress helloIngressRuntime "upload.runtime.frame_receive"
  , mkRuntimeUse "use.upload.begin_ingress" beginIngress beginIngressRuntime "upload.runtime.frame_receive"
  , mkRuntimeUse "use.upload.hello_policy" helloPolicy helloPolicyRuntime "upload.runtime.hello_policy"
  , mkRuntimeUse "use.upload.version_client" versionClient versionClientRuntime "upload.runtime.branch_refinement"
  , mkRuntimeUse "use.upload.begin_policy" beginPolicy beginPolicyRuntime "upload.runtime.begin_policy"
  , mkRuntimeUse "use.upload.payload_receive" payloadExactReceive payloadReceiveRuntime "upload.runtime.receive_exact"
  , mkRuntimeUse "use.upload.payload_send" payloadExactSend payloadSendRuntime "upload.runtime.send_exact"
  , mkRuntimeUse "use.upload.digest" digestMatches digestRuntime "upload.runtime.digest"
  , mkRuntimeUse "use.upload.storage" storageSuccess storageRuntime "upload.runtime.store"
  ]
