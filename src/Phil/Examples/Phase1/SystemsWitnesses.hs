{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.SystemsWitnesses
  ( uploadPhase1StageBundle
  , stevePhase1StageBundle
  , steveHostAbiDecisionId
  , steveHostAbiTargetPrecondition
  , steveHostAbiObligationRevision
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Assurance.Phase0 (phase0UploadLedger)
import Phil.Assurance.Types
import Phil.Core.ProviderQualificationIdentity
  ( CheckedProviderQualificationAdmissionIdentity (..)
  , ProviderQualificationEvidenceIdentityInput (..)
  , QualificationAdmissionRevision (..)
  )
import Phil.Core.Static
import Phil.Core.Syntax (ObligationId (..))
import Phil.Examples.Steve.ProviderQualifications
import Phil.Systems.GenericLowering
import Phil.Systems.IR
import Phil.Systems.Phase1Stage (Phase1StageBundle)

uploadPhase1StageBundle :: Phase1StageBundle
uploadPhase1StageBundle =
  case lowerWitness
      (InstanceKey "instance.phase1.upload")
      (DeclarationKey "decl.phase1.upload")
      "Upload"
      uploadCoreProgram
      uploadRealizationContext of
    Right bundle -> bundle
    Left err -> error ("generic upload lowering failed: " <> err)

stevePhase1StageBundle :: Either String Phase1StageBundle
stevePhase1StageBundle = do
  qualifications <- mapLeft (show . unSteveProviderQualificationError)
    materializeSteveProviderQualifications
  let digestArtifact = steveDigestProviderQualification qualifications
      blobArtifact = steveBlobProviderQualification qualifications
      qualificationRefs = Set.fromList
        [ admissionText (steveProviderCheckedAdmission digestArtifact)
        , admissionText (steveProviderCheckedAdmission blobArtifact)
        ]
      assumptions = Set.unions
        [ qualificationEvidenceAssumptions digestArtifact
        , qualificationEvidenceAssumptions blobArtifact
        ]
      context = steveRealizationContext qualificationRefs assumptions
  lowerWitness
    (InstanceKey "instance.phase1.steve")
    (DeclarationKey "decl.phase1.steve")
    "Steve"
    steveCoreProgram
    context

-- | Witness adapters end at exact checked ArchitectureInstances.  The generic
-- producer receives only that identity, checked Core execution, and explicit
-- realization evidence.  It contains no upload/Steve branch.
lowerWitness
  :: InstanceKey
  -> DeclarationKey
  -> Text
  -> CoreSystemsProgram
  -> GenericRealizationContext
  -> Either String Phase1StageBundle
lowerWitness instanceKey declarationKey displayName program context = do
  checked <- checkedProgramInstance instanceKey declarationKey displayName program
  mapLeft show (lowerGenericSystems checked program context)

checkedProgramInstance
  :: InstanceKey
  -> DeclarationKey
  -> Text
  -> CoreSystemsProgram
  -> Either String CheckedArchitectureInstance
checkedProgramInstance instanceKey declarationKey displayName program = do
  graph <- mapLeft show (instantiateArchitecture instanceKey node)
  maybe
    (Left "witness ArchitectureInstance root missing after construction")
    Right
    (lookupArchitectureInstance instanceKey graph)
  where
    declaration = deriveDeclarationIdentity DeclarationDescriptor
      { declarationPresentation =
          DeclarationPresentation displayName ["phase1", "witness"]
      , declarationKey = declarationKey
      , declarationInterfaceSemantics = SemanticRecord (Map.fromList
          [ ("boundary", SemanticAtom "checked-core-to-systems")
          , ("facts", SemanticUnordered
              (Set.map SemanticAtom (Map.keysSet (coreProgramFacts program))))
          ])
      , declarationDefinitionSemantics = coreSystemsProgramSemanticForm program
      }
    node = ArchitectureNodeSpec
      { architectureNodeDeclaration = declaration
      , architectureNodeStaticBindings = Map.empty
      , architectureNodeRequirements = []
      , architectureNodeChildren = []
      , architectureNodeReferences = []
      }

-- Framed upload ----------------------------------------------------------------

uploadCoreProgram :: CoreSystemsProgram
uploadCoreProgram = CoreSystemsProgram
  { coreProgramLabel = "Upload"
  , coreProgramProfile = CertifiedRelease
  , coreProgramFunctions = Map.fromList
      [ ("UploadServer", uploadServerFunction)
      , ("UploadClient", uploadClientFunction)
      ]
  , coreProgramFacts = Map.fromList
      [ ("hello.complete_recognition", Just revHelloIngress)
      , ("begin.complete_recognition", Just revBeginIngress)
      , ("hello.policy", Just revHelloPolicy)
      , ("version.client_refinement", Just revVersionClient)
      , ("begin.policy", Just revBeginPolicy)
      , ("payload.exact_receive", Just revPayloadReceive)
      , ("payload.exact_send", Just revPayloadSend)
      , ("digest.matches", Just revDigest)
      , ("storage.success", Just revStorage)
      , ("endpoint.typestate", Nothing)
      , ("digest.shared_borrow", Nothing)
      , ("fatal.cleanup", Nothing)
      , ("payload.index_proof", Just revPayloadReceive)
      , ("digest.proof_wrapper", Just revDigest)
      ]
  }

uploadServerFunction :: CoreSystemsFunction
uploadServerFunction = CoreSystemsFunction
  { coreFunctionKey = "UploadServer"
  , coreFunctionEntry = "server.entry"
  , coreFunctionValues = valueMap
      [ value "server.transport" CoreTransportHandle (Just "transport.server")
      , value "server.pending.hello" (CorePendingIngress "Hello") Nothing
      , value "server.frame.hello" (CoreFrameOwner "Hello") (Just "frame.hello")
      , value "server.raw.hello" (CoreBorrowedValue "server.frame.hello") Nothing
      , value "server.has_version" (CoreRuntimeScalar "Bool") Nothing
      , value "server.pending.begin" (CorePendingIngress "Begin") Nothing
      , value "server.frame.begin" (CoreFrameOwner "Begin") (Just "frame.begin")
      , value "server.raw.begin" (CoreBorrowedValue "server.frame.begin") Nothing
      , value "server.payload_choice" (CoreRuntimeScalar "Bool") Nothing
      , value "server.begin_length" (CoreRuntimeScalar "U64") Nothing
      , value "server.payload" (CoreOwnedBuffer "Bytes[begin.length]")
          (Just "payload.server")
      , value "server.payload_view" (CoreBorrowedValue "server.payload") Nothing
      , value "server.upload_id" (CoreRuntimeScalar "UploadId") Nothing
      ]
  , coreFunctionBlocks = blockMap
      [ block "server.entry"
          [ CoreReceiveFrame "frame" "server.pending.hello"
              "server.frame.hello" "server.transport" "Hello"
          , CoreBorrowView "raw-borrow" "server.raw.hello" "server.frame.hello"
          ]
          (CoreSystemsRecognize "hello.complete_recognition"
            "server.pending.hello" "server.raw.hello"
            "server.hello.commit" "server.hello.recognition_failure")
      , block "server.hello.commit"
          [ CoreCommitIngress "session-control"
              "server.pending.hello" "server.transport"
          , CoreEraseFact "erase-ingress" revHelloIngress useEraseHelloPending
          ]
          (CoreSystemsRuntimeCheck "hello.policy" []
            "server.version.choose" "server.hello.policy_failure")
      , block "server.hello.recognition_failure"
          [ CoreDestroyPending "cleanup"
              "server.pending.hello" "server.frame.hello"
          ]
          (CoreSystemsFatal "RecognitionFailure[Hello]")
      , block "server.hello.policy_failure" []
          (CoreSystemsFatal "ValidationFailure[HelloPolicy]")
      , block "server.version.choose"
          [ CoreRuntimeCall "semantic-call" "choose_supported"
              [] ["server.has_version"] Nothing
          ]
          (CoreSystemsBranch "server.has_version"
            "server.version" "server.unsupported")
      , block "server.unsupported"
          [ CoreRuntimeCall "semantic-call" "select unsupported"
              ["server.transport"] [] Nothing
          ]
          (CoreSystemsEnd "failure")
      , block "server.version"
          [ CoreRuntimeCall "semantic-call" "select version"
              ["server.transport"] [] Nothing
          , CoreEraseFact "erase-static" revVersionServer useEraseVersionProof
          , CoreReceiveFrame "frame" "server.pending.begin"
              "server.frame.begin" "server.transport" "Begin"
          , CoreBorrowView "raw-borrow" "server.raw.begin" "server.frame.begin"
          ]
          (CoreSystemsRecognize "begin.complete_recognition"
            "server.pending.begin" "server.raw.begin"
            "server.begin.commit" "server.begin.recognition_failure")
      , block "server.begin.commit"
          [ CoreCommitIngress "session-control"
              "server.pending.begin" "server.transport"
          , CoreEraseFact "erase-ingress" revBeginIngress useEraseBeginPending
          ]
          (CoreSystemsRuntimeCheck "begin.policy" []
            "server.proceed" "server.reject")
      , block "server.begin.recognition_failure"
          [ CoreDestroyPending "cleanup"
              "server.pending.begin" "server.frame.begin"
          ]
          (CoreSystemsFatal "RecognitionFailure[Begin]")
      , block "server.reject"
          [ CoreRuntimeCall "semantic-call" "select reject"
              ["server.transport"] [] Nothing
          ]
          (CoreSystemsEnd "failure")
      , block "server.proceed"
          [ CoreRuntimeCall "semantic-call" "select proceed"
              ["server.transport"] [] Nothing
          , CoreRuntimeCall "semantic-call" "receive payload/cancel label"
              ["server.transport"] ["server.payload_choice"] Nothing
          ]
          (CoreSystemsBranch "server.payload_choice"
            "server.payload" "server.cancel")
      , block "server.cancel" [] (CoreSystemsEnd "cancelled")
      , block "server.payload" []
          (CoreSystemsReceiveExact "payload.exact_receive"
            "server.transport" "server.begin_length" "server.payload"
            "server.digest" "server.early_eof")
      , block "server.early_eof"
          [CoreCleanupPartial "cleanup" "server.payload"]
          (CoreSystemsFatal "EarlyEOF")
      , block "server.digest"
          [ CoreBorrowView "payload-borrow"
              "server.payload_view" "server.payload"
          , CoreEraseFact "erase-payload-index"
              revPayloadReceive useErasePayloadIndex
          ]
          (CoreSystemsRuntimeCheck "digest.matches" ["server.payload_view"]
            "server.store" "server.digest_mismatch")
      , block "server.digest_mismatch"
          [ CoreReleaseOwner "cleanup" "server.payload"
          , CoreRuntimeCall "semantic-call" "select rejected"
              ["server.transport"] [] Nothing
          ]
          (CoreSystemsEnd "failure")
      , block "server.store"
          [CoreEraseFact "erase-digest-proof" revDigest useEraseDigestProof]
          (CoreSystemsStore "storage.success" "server.payload" "server.upload_id"
            "server.accepted" "server.storage_failure")
      , block "server.accepted"
          [ CoreRuntimeCall "semantic-call" "select accepted"
              ["server.transport", "server.upload_id"] [] Nothing
          ]
          (CoreSystemsEnd "success")
      , block "server.storage_failure" [] (CoreSystemsFatal "StorageFailure")
      ]
  }

uploadClientFunction :: CoreSystemsFunction
uploadClientFunction = CoreSystemsFunction
  { coreFunctionKey = "UploadClient"
  , coreFunctionEntry = "client.entry"
  , coreFunctionValues = valueMap
      [ value "client.transport" CoreTransportHandle (Just "transport.client")
      , value "client.payload" (CoreOwnedBuffer "Bytes[payload.length]")
          (Just "payload.client")
      , value "client.version_branch" (CoreRuntimeScalar "Bool") Nothing
      , value "client.begin_branch" (CoreRuntimeScalar "Bool") Nothing
      , value "client.should_cancel" (CoreRuntimeScalar "Bool") Nothing
      , value "client.result_branch" (CoreRuntimeScalar "Bool") Nothing
      ]
  , coreFunctionBlocks = blockMap
      [ block "client.entry"
          [ CoreRuntimeCall "semantic-call" "send Hello"
              ["client.transport"] [] Nothing
          , CoreRuntimeCall "semantic-call" "receive version/unsupported label"
              ["client.transport"] ["client.version_branch"] Nothing
          ]
          (CoreSystemsBranch "client.version_branch"
            "client.version.check" "client.unsupported")
      , block "client.unsupported"
          [CoreReleaseOwner "cleanup" "client.payload"]
          (CoreSystemsEnd "failure")
      , block "client.version.check" []
          (CoreSystemsRuntimeCheck "version.client_refinement" []
            "client.version" "client.version_failure")
      , block "client.version_failure" []
          (CoreSystemsFatal "VersionRefinementFailure")
      , block "client.version"
          [ CoreRuntimeCall "semantic-call" "send Begin"
              ["client.transport"] [] Nothing
          , CoreRuntimeCall "semantic-call" "receive proceed/reject label"
              ["client.transport"] ["client.begin_branch"] Nothing
          ]
          (CoreSystemsBranch "client.begin_branch"
            "client.proceed" "client.reject")
      , block "client.reject"
          [CoreReleaseOwner "cleanup" "client.payload"]
          (CoreSystemsEnd "failure")
      , block "client.proceed"
          [ CoreRuntimeCall "semantic-call" "should_cancel_upload"
              [] ["client.should_cancel"] Nothing
          ]
          (CoreSystemsBranch "client.should_cancel"
            "client.cancel" "client.payload")
      , block "client.cancel"
          [ CoreRuntimeCall "semantic-call" "select cancel"
              ["client.transport"] [] Nothing
          , CoreReleaseOwner "cleanup" "client.payload"
          ]
          (CoreSystemsEnd "cancelled")
      , block "client.payload"
          [ CoreRuntimeCall "semantic-call" "select payload"
              ["client.transport"] [] Nothing
          , CoreRuntimeCall "send-exact" "send_exact"
              ["client.transport", "client.payload"] []
              (Just "payload.exact_send")
          , CoreRuntimeCall "semantic-call" "receive accepted/rejected label"
              ["client.transport"] ["client.result_branch"] Nothing
          ]
          (CoreSystemsBranch "client.result_branch"
            "client.accepted" "client.rejected")
      , block "client.accepted" [] (CoreSystemsEnd "success")
      , block "client.rejected" [] (CoreSystemsEnd "failure")
      ]
  }

uploadRealizationContext :: GenericRealizationContext
uploadRealizationContext = GenericRealizationContext
  { genericContextRevision = "realization-context.upload.host.v2"
  , genericContextSemantics = SemanticRecord (Map.fromList
      [ ("target", SemanticAtom "host")
      , ("profile", SemanticAtom "certified-release")
      , ("source-compatibility", SemanticAtom
          "frozen phase0 semantic graph through generic Core lowering")
      ])
  , genericContextVerifierProfile = "phase1-stage-verifier.v1"
  , genericContextRealizationRefs = Set.singleton "realization:upload.host.v1"
  , genericContextQualificationRefs = Set.empty
  , genericContextAssumptions = Set.empty
  , genericContextDecisions = Map.fromList
      [ ordinaryDecision "session-control" "lower.session.control_flow" RepresentAsControlFlow
      , ordinaryDecision "frame" "lower.ingress.frame_storage" Materialize
      , ordinaryDecision "raw-borrow" "lower.ingress.raw_borrow" Borrow
      , ordinaryDecision "payload-borrow" "lower.payload.digest_borrow" Borrow
      , ordinaryDecision "hello-policy-decision" "lower.check.hello_policy" InsertCheck
      , ordinaryDecision "begin-policy-decision" "lower.check.begin_policy" InsertCheck
      , ordinaryDecision "version-refinement-decision" "lower.check.version_refinement" InsertCheck
      , ordinaryDecision "receive-exact-decision" "lower.check.receive_exact" InsertCheck
      , ordinaryDecision "send-exact" "lower.runtime.send_exact" Retain
      , ordinaryDecision "digest-decision" "lower.runtime.digest" InsertCheck
      , ordinaryDecision "storage-decision" "lower.runtime.store" Retain
      , ordinaryDecision "cleanup" "lower.resource.cleanup" Cleanup
      , ordinaryDecision "erase-ingress" "lower.erase.pending_wrapper" Erase
      , ordinaryDecision "erase-static" "lower.erase.static_branch_proof" Erase
      , ordinaryDecision "erase-payload-index" "lower.erase.payload_index" Erase
      , ordinaryDecision "erase-digest-proof" "lower.erase.digest_proof" Erase
      , ordinaryDecision "semantic-call" "lower.runtime.semantic_call" Retain
      ]
  , genericContextRuntimeSites = Map.fromList
      [ ("hello.complete_recognition", runtimeSite
          (RecognitionBoundary "Hello") revHelloIngress
          "evidence.upload.ingress.hello.runtime" "upload.runtime.frame_receive")
      , ("begin.complete_recognition", runtimeSite
          (RecognitionBoundary "Begin") revBeginIngress
          "evidence.upload.ingress.begin.runtime" "upload.runtime.frame_receive")
      , ("hello.policy", runtimeSite
          (ValidationBoundary "HelloPolicy") revHelloPolicy
          "evidence.upload.hello_policy.runtime" "upload.runtime.hello_policy")
      , ("version.client_refinement", runtimeSite
          (BranchRefinementBoundary "selected-version") revVersionClient
          "evidence.upload.version.client.runtime" "upload.runtime.branch_refinement")
      , ("begin.policy", runtimeSite
          (ValidationBoundary "BeginPolicy") revBeginPolicy
          "evidence.upload.begin_policy.runtime" "upload.runtime.begin_policy")
      , ("payload.exact_receive", runtimeSite
          ExactReceiveBoundary revPayloadReceive
          "evidence.upload.payload.receive.runtime" "upload.runtime.receive_exact")
      , ("payload.exact_send", runtimeSite
          ExactSendBoundary revPayloadSend
          "evidence.upload.payload.send.runtime" "upload.runtime.send_exact")
      , ("digest.matches", runtimeSite
          DigestBoundary revDigest
          "evidence.upload.digest.runtime" "upload.runtime.digest")
      , ("storage.success", runtimeSite
          StorageBoundary revStorage
          "evidence.upload.storage.runtime" "upload.runtime.store")
      ]
  }

ordinaryDecision :: Text -> Text -> LoweringAction -> (Text, GenericDecisionSpec)
ordinaryDecision key decisionName action =
  (key, GenericDecisionSpec
    { genericDecisionId = DecisionId decisionName
    , genericDecisionSourceRepresentation = "checked Core semantic operation"
    , genericDecisionTargetRepresentation = "Systems semantic mechanism"
    , genericDecisionSemanticEntities = [key]
    , genericDecisionAction = action
    , genericDecisionCostClass = Just SemanticRequired
    , genericDecisionCostShape =
        emptyCostShape { costFrequency = Just "per semantic occurrence" }
    , genericDecisionTargetPreconditions = []
    , genericDecisionAssumptions = []
    , genericDecisionDerivedObligations = []
    })

runtimeSite
  :: RuntimeSiteKind
  -> RevisionId
  -> Text
  -> Text
  -> RuntimeSiteRef
runtimeSite kind revision evidence cost =
  RuntimeSiteRef kind revision (EvidenceEntryId evidence) cost

-- Steve -------------------------------------------------------------------------

steveCoreProgram :: CoreSystemsProgram
steveCoreProgram = CoreSystemsProgram
  { coreProgramLabel = "Steve"
  , coreProgramProfile = CheckedRuntime
  , coreProgramFunctions = Map.fromList
      [ ("StevePut", stevePutFunction)
      , ("SteveGet", steveGetFunction)
      ]
  , coreProgramFacts = Map.fromList
      [ ("steve.digest.stable-subject", Nothing)
      , ("steve.digest.sha256-profile", Nothing)
      , ("steve.blob.borrow-preservation", Nothing)
      , ("steve.blob.no-replace", Nothing)
      , ("steve.blob.atomic-visibility", Nothing)
      , ("steve.blob.authority-confinement", Nothing)
      , ("steve.provider.admission-lineage", Nothing)
      ]
  }

stevePutFunction :: CoreSystemsFunction
stevePutFunction = CoreSystemsFunction
  { coreFunctionKey = "StevePut"
  , coreFunctionEntry = "put.entry"
  , coreFunctionValues = valueMap
      [ value "put.candidate" (CoreOwnedBuffer "OwnedBytes")
          (Just "steve.candidate")
      , value "put.digest-view" (CoreBorrowedValue "put.candidate") Nothing
      , value "put.install-view" (CoreBorrowedValue "put.candidate") Nothing
      , value "put.id" (CoreRuntimeScalar "ContentId[SHA256]") Nothing
      ]
  , coreFunctionBlocks = blockMap
      [ block "put.entry" []
          (CoreSystemsRuntimeChoice "DigestProvider.compute"
            ["put.digest-view"] Nothing
            (Map.fromList [("computed", "put.install")]))
      , block "put.install" []
          (CoreSystemsRuntimeChoice "BlobProvider.install-if-absent"
            ["put.id", "put.install-view"] Nothing
            (Map.fromList
              [ ("installed", "put.ok")
              , ("already-exists", "put.ok")
              , ("storage-failure", "put.failure")
              ]))
      , block "put.ok" [CoreTrace "steve.put.commit"] (CoreSystemsEnd "success")
      , block "put.failure" [] (CoreSystemsEnd "storage-failure")
      ]
  }

steveGetFunction :: CoreSystemsFunction
steveGetFunction = CoreSystemsFunction
  { coreFunctionKey = "SteveGet"
  , coreFunctionEntry = "get.entry"
  , coreFunctionValues = valueMap
      [ value "get.id" (CoreRuntimeScalar "ContentId[SHA256]") Nothing
      , value "get.bytes" (CoreOwnedBuffer "OwnedBytes")
          (Just "steve.read-result")
      , value "get.bytes-view" (CoreBorrowedValue "get.bytes") Nothing
      ]
  , coreFunctionBlocks = blockMap
      [ block "get.entry" []
          (CoreSystemsRuntimeChoice "BlobProvider.read" ["get.id"] Nothing
            (Map.fromList
              [ ("found", "get.check")
              , ("not-found", "get.not-found")
              , ("storage-failure", "get.failure")
              ]))
      , block "get.check" []
          (CoreSystemsRuntimeChoice "DigestProvider.check"
            ["get.id", "get.bytes-view"] Nothing
            (Map.fromList
              [ ("accepted", "get.ok")
              , ("rejected", "get.integrity-failure")
              ]))
      , block "get.ok" [CoreTrace "steve.get.commit"] (CoreSystemsEnd "success")
      , block "get.not-found" [] (CoreSystemsEnd "not-found")
      , block "get.integrity-failure" [] (CoreSystemsEnd "integrity-failure")
      , block "get.failure" [] (CoreSystemsEnd "storage-failure")
      ]
  }

steveRealizationContext :: Set Text -> Set Text -> GenericRealizationContext
steveRealizationContext qualificationRefs assumptions = GenericRealizationContext
  { genericContextRevision = "realization-context.steve.host.v2"
  , genericContextSemantics = SemanticRecord (Map.fromList
      [ ("target", SemanticAtom "host")
      , ("providers", SemanticAtom "qualified Steve providers")
      ])
  , genericContextVerifierProfile = "phase1-stage-verifier.v1"
  , genericContextRealizationRefs = Set.singleton "realization:steve.host.v1"
  , genericContextQualificationRefs = qualificationRefs
  , genericContextAssumptions = assumptions
  , genericContextDecisions = Map.singleton "host-abi"
      GenericDecisionSpec
        { genericDecisionId = steveHostAbiDecisionId
        , genericDecisionSourceRepresentation =
            "Steve BlobProvider semantic byte slice"
        , genericDecisionTargetRepresentation =
            "host pointer/length byte-slice ABI"
        , genericDecisionSemanticEntities = ["steve.blob.byte-slice"]
        , genericDecisionAction = ChooseLayout
        , genericDecisionCostClass = Just TargetRequired
        , genericDecisionCostShape =
            emptyCostShape { costFrequency = Just "per provider ABI realization" }
        , genericDecisionTargetPreconditions = [steveHostAbiTargetPrecondition]
        , genericDecisionAssumptions = []
        , genericDecisionDerivedObligations = [steveHostAbiObligationRevision]
        }
  , genericContextRuntimeSites = Map.empty
  }

steveHostAbiDecisionId :: DecisionId
steveHostAbiDecisionId = DecisionId "lower.steve.host-abi"

steveHostAbiTargetPrecondition :: Text
steveHostAbiTargetPrecondition =
  "host BlobProvider byte-slice ABI preserves pointer/length pairing and length range"

steveHostAbiObligationRevision :: RevisionId
steveHostAbiObligationRevision =
  RevisionId "obligation.phase1.steve.host-abi.v1"

-- Shared helpers ----------------------------------------------------------------

value :: Text -> CoreSystemsValueRole -> Maybe Text -> CoreSystemsValue
value key role storage = CoreSystemsValue
  { coreValueKey = key
  , coreValueRole = role
  , coreValueStorageIdentity = storage
  }

valueMap :: [CoreSystemsValue] -> Map Text CoreSystemsValue
valueMap values = Map.fromList [(coreValueKey item, item) | item <- values]

block :: Text -> [CoreSystemsOperation] -> CoreSystemsTerminator -> CoreSystemsBlock
block key operations terminator = CoreSystemsBlock
  { coreBlockKey = key
  , coreBlockOperations = operations
  , coreBlockTerminator = terminator
  }

blockMap :: [CoreSystemsBlock] -> Map Text CoreSystemsBlock
blockMap blocks = Map.fromList [(coreBlockKey item, item) | item <- blocks]

qualificationEvidenceAssumptions
  :: SteveProviderQualificationArtifact
  -> Set Text
qualificationEvidenceAssumptions artifact =
  qualificationEvidenceAssumptionRefs (steveProviderIdentityEvidence artifact)

admissionText :: CheckedProviderQualificationAdmissionIdentity -> Text
admissionText checked = case checkedQualificationAdmissionRevision checked of
  QualificationAdmissionRevision revisionText -> revisionText

uploadRevisionFor :: Text -> RevisionId
uploadRevisionFor obligationName =
  case
    [ revisionId revision
    | revision <- Map.elems (ledgerRevisions phase0UploadLedger)
    , unObligationId (revisionObligationId revision) == obligationName
    ] of
      [revision] -> revision
      _ -> RevisionId ("missing:" <> obligationName)

revHelloIngress, revBeginIngress, revHelloPolicy, revVersionServer :: RevisionId
revVersionClient, revBeginPolicy, revPayloadReceive, revPayloadSend :: RevisionId
revDigest, revStorage :: RevisionId
revHelloIngress = uploadRevisionFor "upload.ingress.hello.complete_recognition"
revBeginIngress = uploadRevisionFor "upload.ingress.begin.complete_recognition"
revHelloPolicy = uploadRevisionFor "upload.hello.policy"
revVersionServer = uploadRevisionFor "upload.version.offered.server_selection"
revVersionClient = uploadRevisionFor "upload.version.offered.client_receive"
revBeginPolicy = uploadRevisionFor "upload.begin.policy"
revPayloadReceive = uploadRevisionFor "upload.payload.exact_length"
revPayloadSend = uploadRevisionFor "upload.payload.exact_length.client_send"
revDigest = uploadRevisionFor "upload.digest.matches"
revStorage = uploadRevisionFor "upload.accepted.storage_success"

useEraseHelloPending, useEraseBeginPending, useEraseVersionProof :: AssuranceUseId
useErasePayloadIndex, useEraseDigestProof :: AssuranceUseId
useEraseHelloPending = AssuranceUseId "use.systems.erase.hello_pending_wrapper"
useEraseBeginPending = AssuranceUseId "use.systems.erase.begin_pending_wrapper"
useEraseVersionProof = AssuranceUseId "use.systems.erase.version_selection_proof"
useErasePayloadIndex = AssuranceUseId "use.systems.erase.payload_length_index"
useEraseDigestProof = AssuranceUseId "use.systems.erase.digest_proof_wrapper"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
