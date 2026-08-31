{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.SystemsWitnesses
  ( uploadPhase1StageBundle
  , stevePhase1StageBundle
  , steveHostAbiDecisionId
  , steveHostAbiTargetPrecondition
  , steveHostAbiObligationRevision
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Assurance.Types (RevisionId (..))
import Phil.Core.ProviderQualificationIdentity
  ( CheckedProviderQualificationAdmissionIdentity (..)
  , ProviderQualificationEvidenceIdentityInput (..)
  , QualificationAdmissionRevision (..)
  )
import Phil.Core.Static
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

-- | Witness adapters end at exact checked ArchitectureInstances. The generic
-- producer receives only that identity, target-abstract checked Core execution,
-- and an explicit realization context. It has no witness-name branch.
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
              (Set.map SemanticAtom (coreProgramFacts program)))
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

uploadCoreProgram :: CoreSystemsProgram
uploadCoreProgram = CoreSystemsProgram
  { coreProgramLabel = "Upload"
  , coreProgramProfile = CheckedRuntime
  , coreProgramFunctions = Map.fromList
      [ ("upload.client", uploadClientFunction)
      , ("upload.server", uploadServerFunction)
      ]
  , coreProgramFacts = Set.fromList
      [ "upload.protocol.exact-progression"
      , "upload.payload.unique-owner"
      , "upload.begin-policy-before-payload"
      , "upload.digest-before-accept"
      , "upload.failure-resource-closure"
      ]
  }

uploadClientFunction :: CoreSystemsFunction
uploadClientFunction = CoreSystemsFunction
  { coreFunctionKey = "upload.client"
  , coreFunctionEntry = "client.start"
  , coreFunctionValues = Map.fromList
      [ ("client.payload", CoreOwnedValue "upload.payload")
      , ("client.payload-view", CoreBorrowedValue "client.payload")
      , ("client.versions", CoreInputValue "SupportedVersions")
      , ("client.digest", CoreInputValue "Digest")
      , ("client.begin", CoreInputValue "Begin")
      , ("client.session", CoreInputValue "UploadSession")
      ]
  , coreFunctionBlocks = blockMap
      [ coreBlock "client.start"
          [coreCall "upload.supported-versions" [] ["client.versions"]]
          (coreChoice "upload.version-choice" ["client.versions"]
            [ ("unsupported", "client.unsupported")
            , ("version", "client.digest")
            ])
      , coreBlock "client.unsupported" [] (CoreSystemsEnd "failure")
      , coreBlock "client.digest"
          [coreCall "upload.digest" ["client.payload-view"] ["client.digest"]]
          (coreChoice "upload.begin-policy" ["client.digest"]
            [ ("reject", "client.reject")
            , ("proceed", "client.cancel")
            ])
      , coreBlock "client.reject" [] (CoreSystemsEnd "failure")
      , coreBlock "client.cancel" []
          (coreChoice "upload.cancel-choice" []
            [ ("cancel", "client.cancelled")
            , ("payload", "client.send")
            ])
      , coreBlock "client.cancelled" [] (CoreSystemsEnd "cancelled")
      , coreBlock "client.send"
          [coreCall "upload.send-exact"
            ["client.payload", "client.session"] ["client.session"]]
          (coreChoice "upload.final-response" ["client.session"]
            [ ("rejected", "client.final-rejected")
            , ("accepted", "client.accepted")
            ])
      , coreBlock "client.final-rejected" [] (CoreSystemsEnd "failure")
      , coreBlock "client.accepted"
          [CoreSystemsTrace "upload.client.accepted"]
          (CoreSystemsEnd "success")
      ]
  }

uploadServerFunction :: CoreSystemsFunction
uploadServerFunction = CoreSystemsFunction
  { coreFunctionKey = "upload.server"
  , coreFunctionEntry = "server.hello"
  , coreFunctionValues = Map.fromList
      [ ("server.session", CoreInputValue "UploadSession")
      , ("server.hello", CoreInputValue "Hello")
      , ("server.begin", CoreInputValue "Begin")
      , ("server.payload", CoreOwnedValue "upload.server.payload")
      , ("server.payload-view", CoreBorrowedValue "server.payload")
      , ("server.digest", CoreInputValue "Digest")
      , ("server.id", CoreInputValue "UploadId")
      ]
  , coreFunctionBlocks = blockMap
      [ coreBlock "server.hello"
          [coreCall "upload.receive-hello"
            ["server.session"] ["server.hello", "server.session"]]
          (coreChoice "upload.hello-policy" ["server.hello"]
            [ ("unsupported", "server.unsupported")
            , ("version", "server.begin")
            ])
      , coreBlock "server.unsupported" [] (CoreSystemsEnd "failure")
      , coreBlock "server.begin"
          [coreCall "upload.receive-begin"
            ["server.session"] ["server.begin", "server.session"]]
          (coreChoice "upload.begin-policy" ["server.begin"]
            [ ("reject", "server.reject")
            , ("proceed", "server.payload")
            ])
      , coreBlock "server.reject" [] (CoreSystemsEnd "failure")
      , coreBlock "server.payload"
          [ coreCall "upload.receive-exact"
              ["server.session"] ["server.payload", "server.session"]
          , coreCall "upload.digest"
              ["server.payload-view"] ["server.digest"]
          ]
          (coreChoice "upload.store"
            ["server.payload", "server.digest"]
            [ ("stored", "server.respond")
            , ("failure", "server.failure")
            ])
      , coreBlock "server.failure" [] (CoreSystemsEnd "failure")
      , coreBlock "server.respond"
          [coreCall "upload.respond"
            ["server.id", "server.session"] ["server.session"]]
          (CoreSystemsEnd "success")
      ]
  }

uploadRealizationContext :: GenericRealizationContext
uploadRealizationContext = GenericRealizationContext
  { genericContextRevision = "realization-context.upload.host.v1"
  , genericContextSemantics = SemanticRecord (Map.fromList
      [ ("target", SemanticAtom "host")
      , ("profile", SemanticAtom "checked-runtime")
      ])
  , genericContextVerifierProfile = "phase1-stage-verifier.v1"
  , genericContextRealizationRefs = Set.singleton "realization:upload.host.v1"
  , genericContextQualificationRefs = Set.empty
  , genericContextAssumptions = Set.singleton "upload.host-runtime-profile.v1"
  , genericContextOperations = Map.fromList
      [ runtime "upload.supported-versions" "supported_versions"
      , runtime "upload.version-choice" "choose_supported"
      , runtime "upload.digest" "sha256"
      , runtime "upload.begin-policy" "BeginPolicy.validate"
      , runtime "upload.cancel-choice" "should_cancel_upload"
      , runtime "upload.send-exact" "send_exact"
      , runtime "upload.final-response" "Upload.final-response"
      , runtime "upload.receive-hello" "receive Hello"
      , runtime "upload.hello-policy" "HelloPolicy.validate"
      , runtime "upload.receive-begin" "receive Begin"
      , runtime "upload.receive-exact" "receive_exact"
      , runtime "upload.store" "store"
      , runtime "upload.respond" "record_upload_id"
      ]
  , genericContextTargetChoices = []
  }
  where
    runtime key name = (key, ordinaryRuntime name)

steveCoreProgram :: CoreSystemsProgram
steveCoreProgram = CoreSystemsProgram
  { coreProgramLabel = "Steve"
  , coreProgramProfile = CheckedRuntime
  , coreProgramFunctions = Map.fromList
      [ ("steve.put", stevePutFunction)
      , ("steve.get", steveGetFunction)
      ]
  , coreProgramFacts = Set.fromList
      [ "steve.digest.stable-subject"
      , "steve.digest.sha256-profile"
      , "steve.blob.borrow-preservation"
      , "steve.blob.no-replace"
      , "steve.blob.atomic-visibility"
      , "steve.blob.authority-confinement"
      , "steve.provider.admission-lineage"
      ]
  }

stevePutFunction :: CoreSystemsFunction
stevePutFunction = CoreSystemsFunction
  { coreFunctionKey = "steve.put"
  , coreFunctionEntry = "put.digest"
  , coreFunctionValues = Map.fromList
      [ ("put.candidate", CoreOwnedValue "steve.candidate")
      , ("put.digest-view", CoreBorrowedValue "put.candidate")
      , ("put.install-view", CoreBorrowedValue "put.candidate")
      , ("put.id", CoreInputValue "ContentId[SHA256]")
      ]
  , coreFunctionBlocks = blockMap
      [ coreBlock "put.digest" []
          (coreChoice "steve.digest.compute" ["put.digest-view"]
            [("computed", "put.install")])
      , coreBlock "put.install" []
          (coreChoice "steve.blob.install-if-absent"
            ["put.id", "put.install-view"]
            [ ("installed", "put.ok")
            , ("already-exists", "put.ok")
            , ("storage-failure", "put.failure")
            ])
      , coreBlock "put.ok"
          [CoreSystemsTrace "steve.put.commit"]
          (CoreSystemsEnd "success")
      , coreBlock "put.failure" [] (CoreSystemsEnd "storage-failure")
      ]
  }

steveGetFunction :: CoreSystemsFunction
steveGetFunction = CoreSystemsFunction
  { coreFunctionKey = "steve.get"
  , coreFunctionEntry = "get.read"
  , coreFunctionValues = Map.fromList
      [ ("get.id", CoreInputValue "ContentId[SHA256]")
      , ("get.bytes", CoreOwnedValue "steve.read-result")
      , ("get.bytes-view", CoreBorrowedValue "get.bytes")
      ]
  , coreFunctionBlocks = blockMap
      [ coreBlock "get.read" []
          (coreChoice "steve.blob.read" ["get.id"]
            [ ("found", "get.check")
            , ("not-found", "get.not-found")
            , ("storage-failure", "get.failure")
            ])
      , coreBlock "get.check" []
          (coreChoice "steve.digest.check" ["get.id", "get.bytes-view"]
            [ ("accepted", "get.ok")
            , ("rejected", "get.integrity-failure")
            ])
      , coreBlock "get.ok"
          [CoreSystemsTrace "steve.get.commit"]
          (CoreSystemsEnd "success")
      , coreBlock "get.not-found" [] (CoreSystemsEnd "not-found")
      , coreBlock "get.integrity-failure" []
          (CoreSystemsEnd "integrity-failure")
      , coreBlock "get.failure" [] (CoreSystemsEnd "storage-failure")
      ]
  }

steveRealizationContext :: Set Text -> Set Text -> GenericRealizationContext
steveRealizationContext qualificationRefs assumptions = GenericRealizationContext
  { genericContextRevision = "realization-context.steve.host.v1"
  , genericContextSemantics = SemanticRecord (Map.fromList
      [ ("target", SemanticAtom "host")
      , ("profile", SemanticAtom "checked-runtime")
      , ("provider-model", SemanticAtom "qualified")
      ])
  , genericContextVerifierProfile = "phase1-stage-verifier.v1"
  , genericContextRealizationRefs = Set.singleton "realization:steve.host.v1"
  , genericContextQualificationRefs = qualificationRefs
  , genericContextAssumptions = assumptions
  , genericContextOperations = Map.fromList
      [ qualifiedRuntime "steve.digest.compute" "DigestProvider.compute"
      , qualifiedRuntime "steve.blob.install-if-absent"
          "BlobProvider.install-if-absent"
      , qualifiedRuntime "steve.blob.read" "BlobProvider.read"
      , qualifiedRuntime "steve.digest.check" "DigestProvider.check"
      ]
  , genericContextTargetChoices =
      [ RealizedTargetChoice
          { realizedTargetDecisionId = steveHostAbiDecisionId
          , realizedTargetSourceRepresentation =
              "Steve BlobProvider semantic byte slice"
          , realizedTargetRepresentation = "host pointer/length byte-slice ABI"
          , realizedTargetSemanticEntities = ["steve.blob.byte-slice"]
          , realizedTargetAction = ChooseLayout
          , realizedTargetCostClass = TargetRequired
          , realizedTargetCostShape = emptyCostShape
          , realizedTargetPreconditions = [steveHostAbiTargetPrecondition]
          , realizedTargetAssumptions = []
          , realizedTargetDerivedObligations = [steveHostAbiObligationRevision]
          , realizedTargetInspectionPlan =
              [ "verify selected host ABI preserves pointer/length pairing"
              , "verify host length representation covers semantic byte length range"
              ]
          }
      ]
  }
  where
    qualifiedRuntime key name =
      (key, (ordinaryRuntime name)
        { realizedOperationQualificationRefs = qualificationRefs
        , realizedOperationAssumptions = assumptions
        })

ordinaryRuntime :: Text -> RealizedOperation
ordinaryRuntime name = RealizedOperation
  { realizedOperationRuntimeName = name
  , realizedOperationQualificationRefs = Set.empty
  , realizedOperationAssumptions = Set.empty
  , realizedOperationCostClass = SemanticRequired
  , realizedOperationCostShape = emptyCostShape
  , realizedOperationTargetPreconditions = []
  , realizedOperationDerivedObligations = []
  }

steveHostAbiDecisionId :: DecisionId
steveHostAbiDecisionId = DecisionId "lower.steve.host-abi"

steveHostAbiTargetPrecondition :: Text
steveHostAbiTargetPrecondition =
  "host BlobProvider byte-slice ABI preserves pointer/length pairing and length range"

steveHostAbiObligationRevision :: RevisionId
steveHostAbiObligationRevision = RevisionId "obligation.phase1.steve.host-abi.v1"

qualificationEvidenceAssumptions
  :: SteveProviderQualificationArtifact
  -> Set Text
qualificationEvidenceAssumptions artifact =
  qualificationEvidenceAssumptionRefs (steveProviderIdentityEvidence artifact)

admissionText :: CheckedProviderQualificationAdmissionIdentity -> Text
admissionText checked = case checkedQualificationAdmissionRevision checked of
  QualificationAdmissionRevision value -> value

coreBlock
  :: Text
  -> [CoreSystemsOperation]
  -> CoreSystemsTerminator
  -> CoreSystemsBlock
coreBlock key operations terminator = CoreSystemsBlock
  { coreBlockKey = key
  , coreBlockOperations = operations
  , coreBlockTerminator = terminator
  }

blockMap :: [CoreSystemsBlock] -> Map.Map Text CoreSystemsBlock
blockMap blocks = Map.fromList
  [(coreBlockKey blockValue, blockValue) | blockValue <- blocks]

coreCall :: Text -> [Text] -> [Text] -> CoreSystemsOperation
coreCall = CoreSystemsCall

coreChoice :: Text -> [Text] -> [(Text, Text)] -> CoreSystemsTerminator
coreChoice key inputs arms = CoreSystemsChoice
  { coreChoiceOperation = key
  , coreChoiceInputs = inputs
  , coreChoiceArms = Map.fromList arms
  }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
