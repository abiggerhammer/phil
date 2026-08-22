{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.Phase0
  ( phase0SystemsArtifact
  , phase0SystemsAssuranceLedger
  , phase0SystemsAssuranceManifest
  , phase0SystemsAssuranceContext
  , phase0SystemsVerificationContext
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Phase0
  ( phase0UploadLedger
  , phase0UploadManifest
  , phase0UploadVerificationContext
  )
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))
import Phil.Systems.IR
import Phil.Systems.Verify (SystemsVerificationContext (..))

phase0SystemsArtifact :: SystemsArtifact
phase0SystemsArtifact = SystemsArtifact
  { systemsArtifactProgram = phase0Program
  , systemsArtifactStageContract = phase0StageContract
  , systemsArtifactLoweringLedger = phase0LoweringLedger
  }

phase0SystemsAssuranceLedger :: AssuranceLedger
phase0SystemsAssuranceLedger = phase0UploadLedger
  { ledgerUses = Map.union systemsErasureUses (ledgerUses phase0UploadLedger) }

phase0SystemsAssuranceManifest :: AssuranceManifest
phase0SystemsAssuranceManifest = provisional
  { manifestId = deriveManifestId phase0SystemsAssuranceLedger provisional }
  where
    provisional = phase0UploadManifest
      { manifestAssuranceUses = Map.keysSet (ledgerUses phase0SystemsAssuranceLedger)
      , manifestLoweringLedgerRoot = loweringLedgerRoot phase0LoweringLedger
      , manifestCompilationProfile = "systems/certified-release/reference"
      }

phase0SystemsAssuranceContext :: VerificationContext
phase0SystemsAssuranceContext = phase0UploadVerificationContext
  { verificationCompilationProfile = manifestCompilationProfile phase0SystemsAssuranceManifest
  , verificationLoweringLedgerRoot = loweringLedgerRoot phase0LoweringLedger
  }

phase0SystemsVerificationContext :: SystemsVerificationContext
phase0SystemsVerificationContext = SystemsVerificationContext
  { systemsAssuranceLedger = phase0SystemsAssuranceLedger
  , systemsAssuranceManifest = phase0SystemsAssuranceManifest
  , systemsAssuranceVerificationContext = phase0SystemsAssuranceContext
  , systemsExpectedRuntimeKinds = runtimeKinds
  , systemsExpectedSourceFacts = Set.fromList
      [ "hello.complete_recognition"
      , "begin.complete_recognition"
      , "hello.policy"
      , "version.client_refinement"
      , "begin.policy"
      , "payload.exact_receive"
      , "payload.exact_send"
      , "digest.matches"
      , "storage.success"
      , "endpoint.typestate"
      , "digest.shared_borrow"
      , "fatal.cleanup"
      , "payload.index_proof"
      , "digest.proof_wrapper"
      ]
  }

phase0Program :: SystemsProgram
phase0Program = SystemsProgram
  { systemsProgramName = "phase0-upload"
  , systemsProgramProfile = CertifiedRelease
  , systemsProgramFunctions = Map.fromList
      [ (systemsFunctionName serverFunction, serverFunction)
      , (systemsFunctionName clientFunction, clientFunction)
      ]
  }

serverFunction :: SystemsFunction
serverFunction = SystemsFunction
  { systemsFunctionName = "UploadServer"
  , systemsFunctionEntry = b "server.entry"
  , systemsFunctionValues = valueMap serverValues
  , systemsFunctionBlocks = blockMap serverBlocks
  }

clientFunction :: SystemsFunction
clientFunction = SystemsFunction
  { systemsFunctionName = "UploadClient"
  , systemsFunctionEntry = b "client.entry"
  , systemsFunctionValues = valueMap clientValues
  , systemsFunctionBlocks = blockMap clientBlocks
  }

serverValues :: [SystemsValue]
serverValues =
  [ owner "server.transport" TransportHandle "transport.server"
  , plain "server.pending.hello" (PendingIngress "Hello")
  , owner "server.frame.hello" (FrameOwner "Hello") "frame.hello"
  , plain "server.raw.hello" (BorrowedSlice (v "server.frame.hello"))
  , plain "server.has_version" (RuntimeScalar "Bool")
  , plain "server.pending.begin" (PendingIngress "Begin")
  , owner "server.frame.begin" (FrameOwner "Begin") "frame.begin"
  , plain "server.raw.begin" (BorrowedSlice (v "server.frame.begin"))
  , plain "server.payload_choice" (RuntimeScalar "Bool")
  , plain "server.begin_length" (RuntimeScalar "U64")
  , owner "server.payload" (OwnedBuffer "Bytes[begin.length]") "payload.server"
  , plain "server.payload_view" (BorrowedSlice (v "server.payload"))
  , plain "server.upload_id" (RuntimeScalar "UploadId")
  ]

clientValues :: [SystemsValue]
clientValues =
  [ owner "client.transport" TransportHandle "transport.client"
  , owner "client.payload" (OwnedBuffer "Bytes[payload.length]") "payload.client"
  , plain "client.version_branch" (RuntimeScalar "Bool")
  , plain "client.begin_branch" (RuntimeScalar "Bool")
  , plain "client.should_cancel" (RuntimeScalar "Bool")
  , plain "client.result_branch" (RuntimeScalar "Bool")
  ]

serverBlocks :: [SystemsBlock]
serverBlocks =
  [ block "server.entry"
      [ OpReceiveFrame
          (v "server.pending.hello") (v "server.frame.hello") (v "server.transport") "Hello" dFrame
      , OpBorrowView (v "server.raw.hello") (v "server.frame.hello") dRawBorrow
      ]
      (TermRecognize
        (v "server.pending.hello") (v "server.raw.hello") helloIngressSite
        (b "server.hello.commit") (b "server.hello.recognition_failure"))
  , block "server.hello.commit"
      [ OpCommitIngress (v "server.pending.hello") (v "server.transport") dSessionControl
      , OpEraseFact revHelloIngress useEraseHelloPending dEraseIngress
      ]
      (TermRuntimeCheck [] helloPolicySite
        (b "server.version.choose") (b "server.hello.policy_failure"))
  , block "server.hello.recognition_failure"
      [ OpDestroyPending (v "server.pending.hello") (v "server.frame.hello") dCleanup ]
      (TermFatal "RecognitionFailure[Hello]")
  , block "server.hello.policy_failure" [] (TermFatal "ValidationFailure[HelloPolicy]")
  , block "server.version.choose"
      [ OpRuntimeCall "choose_supported"
          [] [v "server.has_version"] Nothing dSemanticCall
      ]
      (TermBranch (v "server.has_version") (b "server.version") (b "server.unsupported"))
  , block "server.unsupported"
      [ OpRuntimeCall "select unsupported" [v "server.transport"] [] Nothing dSemanticCall ]
      (TermEnd "failure")
  , block "server.version"
      [ OpRuntimeCall "select version" [v "server.transport"] [] Nothing dSemanticCall
      , OpEraseFact revVersionServer useEraseVersionProof dEraseStatic
      , OpReceiveFrame
          (v "server.pending.begin") (v "server.frame.begin") (v "server.transport") "Begin" dFrame
      , OpBorrowView (v "server.raw.begin") (v "server.frame.begin") dRawBorrow
      ]
      (TermRecognize
        (v "server.pending.begin") (v "server.raw.begin") beginIngressSite
        (b "server.begin.commit") (b "server.begin.recognition_failure"))
  , block "server.begin.commit"
      [ OpCommitIngress (v "server.pending.begin") (v "server.transport") dSessionControl
      , OpEraseFact revBeginIngress useEraseBeginPending dEraseIngress
      ]
      (TermRuntimeCheck [] beginPolicySite
        (b "server.proceed") (b "server.reject"))
  , block "server.begin.recognition_failure"
      [ OpDestroyPending (v "server.pending.begin") (v "server.frame.begin") dCleanup ]
      (TermFatal "RecognitionFailure[Begin]")
  , block "server.reject"
      [ OpRuntimeCall "select reject" [v "server.transport"] [] Nothing dSemanticCall ]
      (TermEnd "failure")
  , block "server.proceed"
      [ OpRuntimeCall "select proceed" [v "server.transport"] [] Nothing dSemanticCall
      , OpRuntimeCall "receive payload/cancel label"
          [v "server.transport"] [v "server.payload_choice"] Nothing dSemanticCall
      ]
      (TermBranch (v "server.payload_choice") (b "server.payload") (b "server.cancel"))
  , block "server.cancel" [] (TermEnd "cancelled")
  , block "server.payload" []
      (TermReceiveExact
        (v "server.transport") (v "server.begin_length") (v "server.payload") payloadReceiveSite
        (b "server.digest") (b "server.early_eof"))
  , block "server.early_eof"
      [ OpCleanupPartial (v "server.payload") dCleanup ]
      (TermFatal "EarlyEOF")
  , block "server.digest"
      [ OpBorrowView (v "server.payload_view") (v "server.payload") dPayloadBorrow
      , OpEraseFact revPayloadReceive useErasePayloadIndex dErasePayloadIndex
      ]
      (TermRuntimeCheck [v "server.payload_view"] digestSite
        (b "server.store") (b "server.digest_mismatch"))
  , block "server.digest_mismatch"
      [ OpReleaseOwner (v "server.payload") dCleanup
      , OpRuntimeCall "select rejected" [v "server.transport"] [] Nothing dSemanticCall
      ]
      (TermEnd "failure")
  , block "server.store"
      [ OpEraseFact revDigest useEraseDigestProof dEraseDigestProof ]
      (TermStore (v "server.payload") (v "server.upload_id") storageSite
        (b "server.accepted") (b "server.storage_failure"))
  , block "server.accepted"
      [ OpRuntimeCall "select accepted" [v "server.transport", v "server.upload_id"] [] Nothing dSemanticCall ]
      (TermEnd "success")
  , block "server.storage_failure" [] (TermFatal "StorageFailure")
  ]

clientBlocks :: [SystemsBlock]
clientBlocks =
  [ block "client.entry"
      [ OpRuntimeCall "send Hello" [v "client.transport"] [] Nothing dSemanticCall
      , OpRuntimeCall "receive version/unsupported label"
          [v "client.transport"] [v "client.version_branch"] Nothing dSemanticCall
      ]
      (TermBranch (v "client.version_branch") (b "client.version.check") (b "client.unsupported"))
  , block "client.unsupported"
      [ OpReleaseOwner (v "client.payload") dCleanup ]
      (TermEnd "failure")
  , block "client.version.check" []
      (TermRuntimeCheck [] versionClientSite
        (b "client.version") (b "client.version_failure"))
  , block "client.version_failure" [] (TermFatal "VersionRefinementFailure")
  , block "client.version"
      [ OpRuntimeCall "send Begin" [v "client.transport"] [] Nothing dSemanticCall
      , OpRuntimeCall "receive proceed/reject label"
          [v "client.transport"] [v "client.begin_branch"] Nothing dSemanticCall
      ]
      (TermBranch (v "client.begin_branch") (b "client.proceed") (b "client.reject"))
  , block "client.reject"
      [ OpReleaseOwner (v "client.payload") dCleanup ]
      (TermEnd "failure")
  , block "client.proceed"
      [ OpRuntimeCall "should_cancel_upload" [] [v "client.should_cancel"] Nothing dSemanticCall ]
      (TermBranch (v "client.should_cancel") (b "client.cancel") (b "client.payload"))
  , block "client.cancel"
      [ OpRuntimeCall "select cancel" [v "client.transport"] [] Nothing dSemanticCall
      , OpReleaseOwner (v "client.payload") dCleanup
      ]
      (TermEnd "cancelled")
  , block "client.payload"
      [ OpRuntimeCall "select payload" [v "client.transport"] [] Nothing dSemanticCall
      , OpRuntimeCall "send_exact" [v "client.transport", v "client.payload"] []
          (Just payloadSendSite) dSendExact
      , OpRuntimeCall "receive accepted/rejected label"
          [v "client.transport"] [v "client.result_branch"] Nothing dSemanticCall
      ]
      (TermBranch (v "client.result_branch") (b "client.accepted") (b "client.rejected"))
  , block "client.accepted" [] (TermEnd "success")
  , block "client.rejected" [] (TermEnd "failure")
  ]

phase0StageContract :: StageContract
phase0StageContract = StageContract
  { stageContractId = "phase0.protocol-boundary-to-systems.v1"
  , stageSourceArtifactDigest = digestText "Phase 0 upload protocol/boundary semantic graph"
  , stageFacts =
      [ runtimeFact "hello.complete_recognition" revHelloIngress evHelloIngressRuntime
      , runtimeFact "begin.complete_recognition" revBeginIngress evBeginIngressRuntime
      , runtimeFact "hello.policy" revHelloPolicy evHelloPolicyRuntime
      , runtimeFact "version.client_refinement" revVersionClient evVersionClientRuntime
      , runtimeFact "begin.policy" revBeginPolicy evBeginPolicyRuntime
      , runtimeFact "payload.exact_receive" revPayloadReceive evPayloadReceiveRuntime
      , runtimeFact "payload.exact_send" revPayloadSend evPayloadSendRuntime
      , runtimeFact "digest.matches" revDigest evDigestRuntime
      , runtimeFact "storage.success" revStorage evStorageRuntime
      , FactTransfer "endpoint.typestate" Nothing (FactTransferred invSessionControl)
      , FactTransfer "digest.shared_borrow" Nothing (FactTransferred invPayloadBorrow)
      , FactTransfer "fatal.cleanup" Nothing (FactTransferred invFatalCleanup)
      , FactTransfer "payload.index_proof" (Just revPayloadReceive) (FactErased useErasePayloadIndex)
      , FactTransfer "digest.proof_wrapper" (Just revDigest) (FactErased useEraseDigestProof)
      ]
  , stageInvariants = Map.fromList
      [ (invSessionControl, "one physical handle; permitted protocol state is represented by CFG reachability")
      , (invPayloadBorrow, "digest view is non-owning and aliases the unique payload owner without copying")
      , (invFatalCleanup, "fatal ingress/transport/storage exits expose no normal successor and perform required cleanup")
      , (invExactLength, "successful receive_exact edge owns exactly begin.length bytes")
      ]
  , stageRequiredEdges =
      [ edge "UploadServer" "server.entry" "server.hello.commit" "recognition success reaches commit"
      , edge "UploadServer" "server.entry" "server.hello.recognition_failure" "recognition failure remains distinct"
      , edge "UploadServer" "server.begin.commit" "server.proceed" "BeginPolicy success precedes proceed"
      , edge "UploadServer" "server.begin.commit" "server.reject" "BeginPolicy failure is validation reject"
      , edge "UploadServer" "server.payload" "server.digest" "exact receive success gates digest"
      , edge "UploadServer" "server.payload" "server.early_eof" "EarlyEOF is fatal transport failure"
      , edge "UploadServer" "server.digest" "server.store" "digest success gates storage"
      , edge "UploadServer" "server.digest" "server.digest_mismatch" "digest mismatch cannot reach accepted"
      , edge "UploadServer" "server.store" "server.accepted" "accepted requires storage success"
      , edge "UploadServer" "server.store" "server.storage_failure" "storage failure has no accepted successor"
      ]
  , stageDerivedObligations = []
  , stageAssumptions =
      [ "runtime primitives satisfy the assumptions selected by the ADR-010 manifest"
      ]
  , stageTraceRelation =
      [ "systems execution projected to ADR-009 semantic events preserves recognition-before-validation ordering"
      , "diagnostic/internal representation steps are unobservable in certified release"
      ]
  , stageResourceFailureRelation =
      [ "recognition failure destroys pending/frame lifecycle and exposes no successor"
      , "EarlyEOF cleans partial payload and terminates"
      , "digest mismatch releases payload before rejected"
      , "store consumes payload on both success/failure by accepted runtime contract"
      ]
  }

phase0LoweringLedger :: LoweringLedger
phase0LoweringLedger = LoweringLedger decisions (deriveLoweringLedgerRoot decisions)
  where
    decisions = Map.fromList [(loweringDecisionId decision, decision) | decision <- loweringDecisions]

loweringDecisions :: [LoweringDecision]
loweringDecisions =
  [ decision dSessionControl RepresentAsControlFlow (Just SemanticRequired)
      "Endpoint[S] / Endpoint[S']" "transport handle + CFG state"
      ["session typestate"] [] [] []
      ["stale session state is unreachable by CFG"] [invSessionControl]
      [] (emptyCostShape { costBranchOrDispatch = Just "ordinary CFG only" })
  , decision dFrame Materialize (Just SemanticRequired)
      "grammar-backed ingress" "transport frame-buffer owner + pending lifecycle"
      ["PendingRecv", "frame storage"] [revHelloIngress, revBeginIngress]
      [evHelloIngressRuntime, evBeginIngressRuntime] []
      ["frame storage remains live through recognition"] []
      ["frame receive and recognition boundary"]
      (emptyCostShape { costAllocationCount = Just "frame buffer as required by transport", costFrequency = Just "per frame" })
  , decision dRawBorrow Borrow (Just SemanticRequired)
      "RawBytes semantic loan" "non-owning frame slice"
      ["raw recognition view"] [] [] []
      ["owner outlives raw view"] [] []
      (emptyCostShape { costBytesCopied = Just "0 expected", costFrequency = Just "per recognized frame" })
  , decision dPayloadBorrow Borrow (Just SemanticRequired)
      "shared loan of OwnedBytes" "non-owning payload slice"
      ["digest input borrow"] [] [] []
      ["unique owner remains live while view is used"] [invPayloadBorrow] []
      (emptyCostShape { costBytesCopied = Just "0 expected", costFrequency = Just "per payload" })
  , decision dHelloPolicy InsertCheck (Just RuntimeAssuranceRequired)
      "runtime-bound HelloPolicy obligation" "validator branch"
      ["HelloPolicy"] [revHelloPolicy] [evHelloPolicyRuntime] []
      ["recognition success precedes policy test"] [] ["HelloPolicy validator"]
      checkCost
  , decision dBeginPolicy InsertCheck (Just RuntimeAssuranceRequired)
      "runtime-bound BeginPolicy obligation" "validator branch"
      ["BeginPolicy"] [revBeginPolicy] [evBeginPolicyRuntime] []
      ["recognition success precedes policy test"] [] ["BeginPolicy validator"]
      checkCost
  , decision dBranchRefinement InsertCheck (Just RuntimeAssuranceRequired)
      "refined version branch payload" "boundary refinement check"
      ["selected version membership"] [revVersionClient] [evVersionClientRuntime] []
      ["failed check does not bind selected"] [] ["version branch refinement"]
      checkCost
  , decision dReceiveExact InsertCheck (Just RuntimeAssuranceRequired)
      "Bytes[toNat(begin.length)] receive" "receive_exact + EarlyEOF edge"
      ["exact payload length"] [revPayloadReceive] [evPayloadReceiveRuntime] []
      ["success owns exactly requested byte count", "failure cleans partial buffer"] [invExactLength, invFatalCleanup]
      ["receive_exact completeness check"]
      (checkCost { costAllocationCount = Just "one payload buffer", costFrequency = Just "per payload" })
  , decision dSendExact Retain (Just SemanticRequired)
      "exact payload transfer" "send_exact transport call"
      ["client exact payload send"] [revPayloadSend] [evPayloadSendRuntime] []
      ["transport success is the only normal successor"] [] ["send_exact"]
      (emptyCostShape { costFrequency = Just "per payload", costBranchOrDispatch = Just "transport success/failure" })
  , decision dDigestCheck InsertCheck (Just SemanticRequired)
      "DigestMatches runtime obligation" "SHA-256 computation + comparison branch"
      ["digest match"] [revDigest] [evDigestRuntime] []
      ["mismatch cannot reach storage/accepted"] [] ["SHA-256 digest validator"]
      (emptyCostShape { costHashOrCryptoWork = Just "SHA-256 over payload bytes", costDynamicCheckCount = Just "1 comparison", costFrequency = Just "per payload" })
  , decision dStorage Retain (Just SemanticRequired)
      "storage-success obligation" "store runtime call + success/failure branch"
      ["accepted requires storage success"] [revStorage] [evStorageRuntime] []
      ["store consumes payload on both arms"] [invFatalCleanup] ["store"]
      (emptyCostShape { costFrequency = Just "per accepted-digest payload", costBranchOrDispatch = Just "success/failure" })
  , decision dCleanup Cleanup (Just SemanticRequired)
      "linear/fatal resource effects" "explicit release/destroy/cleanup paths"
      ["ADR-005 cleanup"] [] [] []
      ["no normal successor after fatal cleanup"] [invFatalCleanup] []
      (emptyCostShape { costFrequency = Just "failure/terminal path" })
  , decision dEraseIngress Erase (Just SemanticRequired)
      "PendingRecv proof/typestate wrapper" "frame owner + CFG lifecycle"
      ["pending ingress semantic wrapper"] [revHelloIngress, revBeginIngress]
      [evHelloIngressKernel, evBeginIngressKernel] [useEraseHelloPending, useEraseBeginPending]
      ["runtime ingress mechanism remains"] [invSessionControl] [] emptyCostShape
  , decision dEraseStatic Erase (Just SemanticRequired)
      "static branch-selection proof" "no runtime proof object"
      ["version selection evidence"] [revVersionServer] [evVersionServerKernel] [useEraseVersionProof]
      ["branch choice already constrained by checked Core"] [] [] emptyCostShape
  , decision dErasePayloadIndex Erase (Just SemanticRequired)
      "dependent Bytes index proof" "payload owner + exact-length control invariant"
      ["payload exact-length proof"] [revPayloadReceive] [evPayloadReceiveKernel] [useErasePayloadIndex]
      ["exact receive runtime mechanism remains"] [invExactLength] [] emptyCostShape
  , decision dEraseDigestProof Erase (Just SemanticRequired)
      "Proof[DigestMatches] wrapper" "digest-success control edge"
      ["digest evidence wrapper"] [revDigest] [evDigestKernel, evDigestRuntime] [useEraseDigestProof]
      ["runtime digest check remains and success edge gates storage"] [] [] emptyCostShape
  , decision dSemanticCall Retain (Just SemanticRequired)
      "source/protocol runtime operation" "ordinary runtime call/control flow"
      ["protocol/application operation"] [] [] [] [] [] []
      (emptyCostShape { costFrequency = Just "as demanded by source control flow" })
  ]
  where
    checkCost = emptyCostShape
      { costDynamicCheckCount = Just "1 logical check"
      , costBranchOrDispatch = Just "success/failure"
      , costFrequency = Just "per relevant message"
      }

systemsErasureUses :: Map AssuranceUseId AssuranceUse
systemsErasureUses = Map.fromList
  [ pair useEraseHelloPending revHelloIngress [evHelloIngressKernel, evHelloIngressRuntime]
  , pair useEraseBeginPending revBeginIngress [evBeginIngressKernel, evBeginIngressRuntime]
  , pair useEraseVersionProof revVersionServer [evVersionServerKernel]
  , pair useErasePayloadIndex revPayloadReceive [evPayloadReceiveKernel]
  , pair useEraseDigestProof revDigest [evDigestKernel, evDigestRuntime]
  ]
  where
    pair useId revision entries = (useId, seal ErasureUse
      { assuranceUseId = useId
      , assuranceUseDigest = Digest ""
      , useObligationRevision = revision
      , useEvidenceEntries = entries
      })
    seal use = use { assuranceUseDigest = deriveAssuranceUseDigest use }

runtimeKinds :: Map EvidenceEntryId RuntimeSiteKind
runtimeKinds = Map.fromList
  [ (evHelloIngressRuntime, RecognitionBoundary "Hello")
  , (evBeginIngressRuntime, RecognitionBoundary "Begin")
  , (evHelloPolicyRuntime, ValidationBoundary "HelloPolicy")
  , (evVersionClientRuntime, BranchRefinementBoundary "selected-version")
  , (evBeginPolicyRuntime, ValidationBoundary "BeginPolicy")
  , (evPayloadReceiveRuntime, ExactReceiveBoundary)
  , (evPayloadSendRuntime, ExactSendBoundary)
  , (evDigestRuntime, DigestBoundary)
  , (evStorageRuntime, StorageBoundary)
  ]

helloIngressSite, beginIngressSite, helloPolicySite, versionClientSite, beginPolicySite :: RuntimeSiteRef
payloadReceiveSite, payloadSendSite, digestSite, storageSite :: RuntimeSiteRef
helloIngressSite = site (RecognitionBoundary "Hello") revHelloIngress evHelloIngressRuntime "upload.runtime.frame_receive"
beginIngressSite = site (RecognitionBoundary "Begin") revBeginIngress evBeginIngressRuntime "upload.runtime.frame_receive"
helloPolicySite = site (ValidationBoundary "HelloPolicy") revHelloPolicy evHelloPolicyRuntime "upload.runtime.hello_policy"
versionClientSite = site (BranchRefinementBoundary "selected-version") revVersionClient evVersionClientRuntime "upload.runtime.branch_refinement"
beginPolicySite = site (ValidationBoundary "BeginPolicy") revBeginPolicy evBeginPolicyRuntime "upload.runtime.begin_policy"
payloadReceiveSite = site ExactReceiveBoundary revPayloadReceive evPayloadReceiveRuntime "upload.runtime.receive_exact"
payloadSendSite = site ExactSendBoundary revPayloadSend evPayloadSendRuntime "upload.runtime.send_exact"
digestSite = site DigestBoundary revDigest evDigestRuntime "upload.runtime.digest"
storageSite = site StorageBoundary revStorage evStorageRuntime "upload.runtime.store"

site :: RuntimeSiteKind -> RevisionId -> EvidenceEntryId -> Text -> RuntimeSiteRef
site = RuntimeSiteRef

runtimeFact :: Text -> RevisionId -> EvidenceEntryId -> FactTransfer
runtimeFact name revision evidence = FactTransfer name (Just revision) (FactRuntimeRetained evidence)

edge :: Text -> Text -> Text -> Text -> RequiredControlEdge
edge functionName from to reason = RequiredControlEdge functionName (b from) (b to) reason

decision
  :: DecisionId
  -> LoweringAction
  -> Maybe CostClass
  -> Text
  -> Text
  -> [Text]
  -> [RevisionId]
  -> [EvidenceEntryId]
  -> [AssuranceUseId]
  -> [Text]
  -> [InvariantId]
  -> [Text]
  -> CostShape
  -> LoweringDecision
decision decisionId action costClass source target entities revisions evidence uses preserved transferred residue costShape =
  seal LoweringDecision
    { loweringDecisionId = decisionId
    , loweringDecisionDigest = Digest ""
    , loweringSourceRepresentation = source
    , loweringTargetRepresentation = target
    , loweringSemanticEntities = entities
    , loweringObligationRevisions = revisions
    , loweringAssuranceEntries = evidence
    , loweringAssuranceUses = uses
    , loweringAction = action
    , loweringRepresentationBefore = source
    , loweringRepresentationAfter = target
    , loweringInvariantsPreserved = preserved
    , loweringInvariantsTransferred = transferred
    , loweringRuntimeResidue = residue
    , loweringCostClass = costClass
    , loweringCostShape = costShape
    , loweringTargetPreconditions = []
    , loweringAssumptions = []
    , loweringDerivedObligations = []
    , loweringInspectionPlan = []
    }
  where
    seal value = value { loweringDecisionDigest = deriveLoweringDecisionDigest value }

block :: Text -> [SystemsOp] -> SystemsTerminator -> SystemsBlock
block name operations terminator = SystemsBlock (b name) operations terminator

blockMap :: [SystemsBlock] -> Map BlockId SystemsBlock
blockMap blocks = Map.fromList [(systemsBlockId value, value) | value <- blocks]

valueMap :: [SystemsValue] -> Map ValueId SystemsValue
valueMap values = Map.fromList [(systemsValueId value, value) | value <- values]

plain :: Text -> SystemsValueRole -> SystemsValue
plain name role = SystemsValue (v name) role Nothing

owner :: Text -> SystemsValueRole -> Text -> SystemsValue
owner name role storage = SystemsValue (v name) role (Just storage)

v :: Text -> ValueId
v = ValueId

b :: Text -> BlockId
b = BlockId

d :: Text -> DecisionId
d = DecisionId

inv :: Text -> InvariantId
inv = InvariantId

dSessionControl, dFrame, dRawBorrow, dPayloadBorrow, dHelloPolicy, dBeginPolicy :: DecisionId
dBranchRefinement, dReceiveExact, dSendExact, dDigestCheck, dStorage, dCleanup :: DecisionId
dEraseIngress, dEraseStatic, dErasePayloadIndex, dEraseDigestProof, dSemanticCall :: DecisionId
dSessionControl = d "lower.session.control_flow"
dFrame = d "lower.ingress.frame_storage"
dRawBorrow = d "lower.ingress.raw_borrow"
dPayloadBorrow = d "lower.payload.digest_borrow"
dHelloPolicy = d "lower.check.hello_policy"
dBeginPolicy = d "lower.check.begin_policy"
dBranchRefinement = d "lower.check.version_refinement"
dReceiveExact = d "lower.check.receive_exact"
dSendExact = d "lower.runtime.send_exact"
dDigestCheck = d "lower.runtime.digest"
dStorage = d "lower.runtime.store"
dCleanup = d "lower.resource.cleanup"
dEraseIngress = d "lower.erase.pending_wrapper"
dEraseStatic = d "lower.erase.static_branch_proof"
dErasePayloadIndex = d "lower.erase.payload_index"
dEraseDigestProof = d "lower.erase.digest_proof"
dSemanticCall = d "lower.runtime.semantic_call"

invSessionControl, invPayloadBorrow, invFatalCleanup, invExactLength :: InvariantId
invSessionControl = inv "invariant.session.control_flow"
invPayloadBorrow = inv "invariant.payload.borrow_no_copy"
invFatalCleanup = inv "invariant.failure.cleanup"
invExactLength = inv "invariant.payload.exact_length"

useEraseHelloPending, useEraseBeginPending, useEraseVersionProof :: AssuranceUseId
useErasePayloadIndex, useEraseDigestProof :: AssuranceUseId
useEraseHelloPending = AssuranceUseId "use.systems.erase.hello_pending_wrapper"
useEraseBeginPending = AssuranceUseId "use.systems.erase.begin_pending_wrapper"
useEraseVersionProof = AssuranceUseId "use.systems.erase.version_selection_proof"
useErasePayloadIndex = AssuranceUseId "use.systems.erase.payload_length_index"
useEraseDigestProof = AssuranceUseId "use.systems.erase.digest_proof_wrapper"

revHelloIngress, revBeginIngress, revHelloPolicy, revVersionServer, revVersionClient :: RevisionId
revBeginPolicy, revPayloadReceive, revPayloadSend, revDigest, revStorage :: RevisionId
revHelloIngress = revisionFor "upload.ingress.hello.complete_recognition"
revBeginIngress = revisionFor "upload.ingress.begin.complete_recognition"
revHelloPolicy = revisionFor "upload.hello.policy"
revVersionServer = revisionFor "upload.version.offered.server_selection"
revVersionClient = revisionFor "upload.version.offered.client_receive"
revBeginPolicy = revisionFor "upload.begin.policy"
revPayloadReceive = revisionFor "upload.payload.exact_length"
revPayloadSend = revisionFor "upload.payload.exact_length.client_send"
revDigest = revisionFor "upload.digest.matches"
revStorage = revisionFor "upload.accepted.storage_success"

revisionFor :: Text -> RevisionId
revisionFor obligationName =
  case
    [ revisionId revision
    | revision <- Map.elems (ledgerRevisions phase0UploadLedger)
    , unObligationId (revisionObligationId revision) == obligationName
    ] of
      [revision] -> revision
      _ -> RevisionId ("missing:" <> obligationName)

evHelloIngressKernel, evHelloIngressRuntime, evBeginIngressKernel, evBeginIngressRuntime :: EvidenceEntryId
evHelloPolicyRuntime, evVersionServerKernel, evVersionClientRuntime, evBeginPolicyRuntime :: EvidenceEntryId
evPayloadReceiveKernel, evPayloadReceiveRuntime, evPayloadSendRuntime, evDigestKernel, evDigestRuntime, evStorageRuntime :: EvidenceEntryId
evHelloIngressKernel = EvidenceEntryId "evidence.upload.ingress.hello.kernel"
evHelloIngressRuntime = EvidenceEntryId "evidence.upload.ingress.hello.runtime"
evBeginIngressKernel = EvidenceEntryId "evidence.upload.ingress.begin.kernel"
evBeginIngressRuntime = EvidenceEntryId "evidence.upload.ingress.begin.runtime"
evHelloPolicyRuntime = EvidenceEntryId "evidence.upload.hello_policy.runtime"
evVersionServerKernel = EvidenceEntryId "evidence.upload.version.server.kernel"
evVersionClientRuntime = EvidenceEntryId "evidence.upload.version.client.runtime"
evBeginPolicyRuntime = EvidenceEntryId "evidence.upload.begin_policy.runtime"
evPayloadReceiveKernel = EvidenceEntryId "evidence.upload.payload.receive.kernel"
evPayloadReceiveRuntime = EvidenceEntryId "evidence.upload.payload.receive.runtime"
evPayloadSendRuntime = EvidenceEntryId "evidence.upload.payload.send.runtime"
evDigestKernel = EvidenceEntryId "evidence.upload.digest.kernel"
evDigestRuntime = EvidenceEntryId "evidence.upload.digest.runtime"
evStorageRuntime = EvidenceEntryId "evidence.upload.storage.runtime"
