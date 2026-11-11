{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Compiler.SourceCorePolicy
import Phil.Compiler.SourceSystems
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  , identityInstanceRevision
  , identityInstanceKey
  , InstanceKey (..)
  )
import Phil.Core.Syntax (Mode (..), Ty (..))
import Phil.Examples.Phase1.StageClosureWitnesses
  ( steveStageClosureBundle
  , uploadStageClosureBundle
  )
import Phil.Examples.Phase1.ProviderCallWitnesses
  ( steveProviderCallExpectations
  , uploadProviderCallExpectations
  )
import Phil.Verification.VerifiedStageClosureProduction
import Phil.Systems.StageClosure
  ( StageClosureBundle
  , concreteSubjectStage
  , nextStageSubjectStage
  , stageClosureConcrete
  , stageClosureNextStage
  , verifyStageClosureBundle
  )
import Phil.Systems.SubjectCorrespondence (subjectStageBase)
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveCoreProgram
  , steveQualifiedRealizationContext
  , uploadCoreProgram
  , uploadRealizationContext
  )
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.LLVM.Phase0 (phase0LLVMTarget)
import Phil.Surface.Check
import Phil.Surface.Lineage
  ( DeclarationSiteId (..)
  , InstanceLineageSiteId (..)
  , PortableInstanceLineage (..)
  , PortableSourceBundle (..)
  , PortableSourceUnit (..)
  , SourceUnitId (..)
  , canonicalGrammarRevisionV1
  )
import Phil.Surface.Phase0 (phase0EnvironmentFor)
import Phil.Systems.GenericLowering
  ( CoreSystemsProgram (..)
  , GenericRealizationContext
  , coreSystemsProgramSemanticForm
  )
import Phil.Systems.IR (systemsArtifactDigest)
import Phil.Systems.Phase1Stage
  ( phase1StageInstanceRevision
  , phase1StageSystemsArtifact
  , verifyPhase1StageBundle
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  uploadClient <- TextIO.readFile "examples/upload/client.phil"
  uploadServer <- TextIO.readFile "examples/upload/server.phil"
  stevePut <- TextIO.readFile "examples/steve/put.phil"
  steveGet <- TextIO.readFile "examples/steve/get.phil"
  results <- sequence
    [ test "INT-001 framed upload traverses ordinary source through shared backend"
        (uploadE2E uploadClient uploadServer)
    , test "INT-001 Steve traverses ordinary source through shared backend"
        (steveE2E stevePut steveGet)
    , test "INT-001 Upload source-owned producer retains exact K/I and whole stage"
        (uploadVerifiedProducer uploadClient uploadServer)
    , test "INT-001 Steve source-owned producer retains exact K/I and whole stage"
        (steveVerifiedProducer stevePut steveGet)
    , test "INT-001 source-owned producer refuses unlisted occurrence site"
        (verifiedProducerRejectsWrongSite uploadClient uploadServer)
    , test "P6 Upload whole StageClosure built from sealed ordinary source"
        (uploadVerifiedStageClosure uploadClient uploadServer)
    , test "P6 Steve whole StageClosure built from sealed ordinary source"
        (steveVerifiedStageClosure stevePut steveGet)
    , test "P6 Steve stage config cannot borrow Upload producer"
        (verifiedStageRejectsWrongConcrete uploadClient uploadServer)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadE2E :: Text -> Text -> Either String ()
uploadE2E clientSource serverSource = do
  architecture <- checkedUploadArchitecture clientSource serverSource
  runWitness architecture uploadPolicy uploadCoreProgram uploadRealizationContext

steveE2E :: Text -> Text -> Either String ()
steveE2E putSource getSource = do
  architecture <- checkedSteveArchitecture putSource getSource
  context <- steveQualifiedRealizationContext
  runWitness architecture stevePolicy steveCoreProgram context

-- | The integration runner is deliberately witness-neutral.  Program-specific
-- source environments, correspondence policy, checked Core, and realization
-- context are data supplied at the boundary; the sealing, Systems lowering,
-- and LLVM backend path has no Upload/Steve discriminator.
runWitness
  :: CheckedSourceArchitecture
  -> SourceCoreCorrespondencePolicy
  -> CoreSystemsProgram
  -> GenericRealizationContext
  -> Either String ()
runWitness architecture policy program context = do
  admission <- mapLeft show
    (prepareSourceSystemsAdmission policy architecture program)
  assert
    (sourceSystemsProgramSemantics admission == coreSystemsProgramSemanticForm program)
    "sealed source/Core admission changed exact Core semantic identity"
  bundle <- mapLeft show (lowerSourceSystems admission context)
  mapLeft show (verifyPhase1StageBundle bundle)
  assert
    (phase1StageInstanceRevision bundle
      == identityInstanceRevision (sourceSystemsArchitectureIdentity admission))
    "generic Systems lowering did not retain source-derived Architecture identity"
  let systemsArtifact = phase1StageSystemsArtifact bundle
      llvmArtifact = lowerSystemsConservative phase0LLVMTarget systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
  assert
    (Map.keysSet (llvmFunctions llvmModule) == Map.keysSet (coreProgramFunctions program))
    "shared LLVM backend changed the admitted function domain"
  assert
    (llvmArtifactText llvmArtifact == renderLLVMModule llvmModule)
    "shared LLVM backend artifact text is not canonical for its emitted module"
  assert
    (llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      == systemsArtifactDigest systemsArtifact)
    "shared LLVM backend did not bind the exact admitted Systems artifact"

-- These attest only actual ordinary-source/Core-to-Systems production,
-- not the independent StageClosure or final release's historical provenance.
uploadVerifiedProducer :: Text -> Text -> Either String ()
uploadVerifiedProducer clientSource serverSource = do
  clientEnvironment <- mapLeft show (phase0EnvironmentFor "client.phil")
  serverEnvironment <- mapLeft show (phase0EnvironmentFor "server.phil")
  let environments = Map.fromList
        [ (uploadClientDeclaration, clientEnvironment)
        , (uploadServerDeclaration, serverEnvironment) ]
  produced <- mapLeft show $ produceVerifiedSourceSystems
    uploadRoots environments
    (Map.singleton "program:upload" (InstanceLineageSiteId "instance.upload"))
    uploadPolicy (uploadBundle clientSource serverSource)
    uploadCoreProgram uploadRealizationContext
  architecture <- checkedUploadArchitecture clientSource serverSource
  admitted <- mapLeft show $
    prepareSourceSystemsAdmission uploadPolicy architecture uploadCoreProgram
  original <- mapLeft show (lowerSourceSystems admitted uploadRealizationContext)
  let occurrence = verifiedSourceSystemsArchitectureIdentity produced
      fullStage = verifiedSourceSystemsStage produced
  mapLeft show (verifyPhase1StageBundle fullStage)
  assert (identityInstanceKey occurrence == InstanceKey "inst:phase1.upload")
    "source-owned producer lost Upload occurrence K"
  assert (identityInstanceRevision occurrence == phase1StageInstanceRevision fullStage)
    "source-owned producer lost Upload occurrence I"
  assert (fullStage == original)
    "source-owned producer changed complete Upload stage"

steveVerifiedProducer :: Text -> Text -> Either String ()
steveVerifiedProducer putSource getSource = do
  context <- steveQualifiedRealizationContext
  produced <- mapLeft show $ produceVerifiedSourceSystems
    steveRoots steveEnvironments
    (Map.singleton "program:steve" (InstanceLineageSiteId "instance.steve"))
    stevePolicy (steveBundle putSource getSource) steveCoreProgram context
  architecture <- checkedSteveArchitecture putSource getSource
  admitted <- mapLeft show $
    prepareSourceSystemsAdmission stevePolicy architecture steveCoreProgram
  original <- mapLeft show (lowerSourceSystems admitted context)
  let occurrence = verifiedSourceSystemsArchitectureIdentity produced
      fullStage = verifiedSourceSystemsStage produced
  mapLeft show (verifyPhase1StageBundle fullStage)
  assert (identityInstanceKey occurrence == InstanceKey "inst:phase1.steve")
    "source-owned producer lost Steve occurrence K"
  assert (identityInstanceRevision occurrence == phase1StageInstanceRevision fullStage)
    "source-owned producer lost Steve occurrence I"
  assert (fullStage == original)
    "source-owned producer changed complete Steve stage"

verifiedProducerRejectsWrongSite :: Text -> Text -> Either String ()
verifiedProducerRejectsWrongSite clientSource serverSource = do
  clientEnvironment <- mapLeft show (phase0EnvironmentFor "client.phil")
  serverEnvironment <- mapLeft show (phase0EnvironmentFor "server.phil")
  let environments = Map.fromList
        [ (uploadClientDeclaration, clientEnvironment)
        , (uploadServerDeclaration, serverEnvironment) ]
      nonexistent = InstanceLineageSiteId "instance.unlisted"
  case produceVerifiedSourceSystems
      uploadRoots environments
      (Map.singleton "program:upload" nonexistent)
      uploadPolicy (uploadBundle clientSource serverSource)
      uploadCoreProgram uploadRealizationContext of
    Left (VerifiedSourceArchitectureRejected
        (SourceArchitectureInstanceLineageMissing missingSite))
      | missingSite == nonexistent -> Right ()
    other -> Left ("unlisted source producer site not refused: " <> show other)


-- The legacy StageClosure witness is configuration only, not a production
-- authority. Reconstruct every stage from an independently checked ordinary
-- source producer with the REAL checked source occurrence.
verifiedUploadProduction
  :: Text -> Text -> Either String VerifiedSourceSystemsProduction
verifiedUploadProduction clientSource serverSource = do
  clientEnvironment <- mapLeft show (phase0EnvironmentFor "client.phil")
  serverEnvironment <- mapLeft show (phase0EnvironmentFor "server.phil")
  mapLeft show $ produceVerifiedSourceSystems
    uploadRoots
    (Map.fromList
      [ (uploadClientDeclaration, clientEnvironment)
      , (uploadServerDeclaration, serverEnvironment) ])
    (Map.singleton "program:upload" (InstanceLineageSiteId "instance.upload"))
    uploadPolicy (uploadBundle clientSource serverSource)
    uploadCoreProgram uploadRealizationContext

verifiedSteveProduction
  :: Text -> Text -> Either String VerifiedSourceSystemsProduction
verifiedSteveProduction putSource getSource = do
  context <- steveQualifiedRealizationContext
  mapLeft show $ produceVerifiedSourceSystems
    steveRoots steveEnvironments
    (Map.singleton "program:steve" (InstanceLineageSiteId "instance.steve"))
    stevePolicy (steveBundle putSource getSource)
    steveCoreProgram context

uploadVerifiedStageClosure :: Text -> Text -> Either String ()
uploadVerifiedStageClosure clientSource serverSource = do
  production <- verifiedUploadProduction clientSource serverSource
  template <- uploadStageClosureBundle
  retained <- mapLeft show
    (produceVerifiedStageClosure production uploadProviderCallExpectations template)
  assert (verifiedStageClosureSourceProduction retained == production)
    "Upload lost sealed producer"
  assertStageFromProduction production (verifiedStageClosureSelected retained)

steveVerifiedStageClosure :: Text -> Text -> Either String ()
steveVerifiedStageClosure putSource getSource = do
  production <- verifiedSteveProduction putSource getSource
  template <- steveStageClosureBundle
  retained <- mapLeft show
    (produceVerifiedStageClosure production steveProviderCallExpectations template)
  assert (verifiedStageClosureSourceProduction retained == production)
    "Steve lost sealed producer"
  assertStageFromProduction production (verifiedStageClosureSelected retained)

assertStageFromProduction
  :: VerifiedSourceSystemsProduction
  -> StageClosureBundle
  -> Either String ()
assertStageFromProduction production selected = do
  mapLeft show (verifyStageClosureBundle selected)
  let sourceStage = verifiedSourceSystemsStage production
      concreteStage = subjectStageBase
        (concreteSubjectStage (stageClosureConcrete selected))
      nextStage = subjectStageBase
        (nextStageSubjectStage (stageClosureNextStage selected))
  assert (concreteStage == sourceStage)
    "concrete closure arm substituted the entire produced base"
  assert (nextStage == sourceStage)
    "next-stage closure arm substituted the entire produced base"

verifiedStageRejectsWrongConcrete :: Text -> Text -> Either String ()
verifiedStageRejectsWrongConcrete clientSource serverSource = do
  production <- verifiedUploadProduction clientSource serverSource
  steveTemplate <- steveStageClosureBundle
  case produceVerifiedStageClosure
      production steveProviderCallExpectations steveTemplate of
    Left _ -> Right ()
    Right _ -> Left "Steve stage unexpectedly accepted Upload producer"

-- Framed upload ----------------------------------------------------------------

checkedUploadArchitecture :: Text -> Text -> Either String CheckedSourceArchitecture
checkedUploadArchitecture clientSource serverSource = do
  clientEnvironment <- mapLeft show (phase0EnvironmentFor "client.phil")
  serverEnvironment <- mapLeft show (phase0EnvironmentFor "server.phil")
  checked <- mapLeft show $ checkPortableSourceBundle
    uploadRoots
    (Map.fromList
      [ (uploadClientDeclaration, clientEnvironment)
      , (uploadServerDeclaration, serverEnvironment)
      ])
    (uploadBundle clientSource serverSource)
  mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:upload" (InstanceLineageSiteId "instance.upload"))
    checked

uploadBundle :: Text -> Text -> PortableSourceBundle
uploadBundle clientSource serverSource = PortableSourceBundle
  { portableGrammarRevision = canonicalGrammarRevisionV1
  , portableSelectedProgramRoot = "program:upload"
  , portableSourceUnits =
      [ PortableSourceUnit
          (SourceUnitId "unit.upload.client")
          (DeclarationSiteId "site.upload.client")
          (Just "decl:upload.client")
          clientSource
      , PortableSourceUnit
          (SourceUnitId "unit.upload.server")
          (DeclarationSiteId "site.upload.server")
          (Just "decl:upload.server")
          serverSource
      ]
  , portableInstanceLineage =
      [ PortableInstanceLineage
          (InstanceLineageSiteId "instance.upload")
          "inst:phase1.upload"
      ]
  , portableProcessLineage = []
  }

uploadRoots :: SourceRootMap
uploadRoots = Map.singleton "program:upload" uploadServerDeclaration

uploadClientDeclaration, uploadServerDeclaration :: DeclarationKey
uploadClientDeclaration = DeclarationKey "decl:upload.client"
uploadServerDeclaration = DeclarationKey "decl:upload.server"

uploadPolicy :: SourceCoreCorrespondencePolicy
uploadPolicy = SourceCoreCorrespondencePolicy
  { sourceCoreCallPolicy = Map.fromList
      [ (site "UploadClient" 0, SourceCallRuntimeOperation "supported_versions")
      , (site "UploadClient" 1, SourceCallErasedStatic)
      , (site "UploadClient" 2, SourceCallRuntimeOperation "sha256")
      , (site "UploadClient" 3, SourceCallRuntimeOperation "should_cancel_upload")
      , (site "UploadClient" 4, SourceCallRuntimeOperation "record_upload_id")
      , (site "UploadServer" 0, SourceCallRuntimeOperation "choose_supported")
      , (site "UploadServer" 1, SourceCallFact "storage.success")
      ]
  , sourceCoreBranchPolicy = Map.fromList
      [ (site "UploadClient" 0,
          branch "client.entry"
            [("unsupported", "client.unsupported"), ("version", "client.version.check")])
      , (site "UploadClient" 1,
          branch "client.version"
            [("proceed", "client.proceed"), ("reject", "client.reject")])
      , (site "UploadClient" 2,
          branch "client.proceed"
            [("false", "client.payload"), ("true", "client.cancel")])
      , (site "UploadClient" 3,
          branch "client.payload"
            [("accepted", "client.accepted"), ("rejected", "client.rejected")])
      , (site "UploadServer" 0,
          SourceBranchReceiveFrameNonreturningFallback "server.entry")
      , (site "UploadServer" 1,
          branch "server.entry"
            [("accepted", "server.hello.commit"),
             ("rejected", "server.hello.recognition_failure")])
      , (site "UploadServer" 2,
          branch "server.hello.commit"
            [("accepted", "server.version.choose"),
             ("rejected", "server.hello.policy_failure")])
      , (site "UploadServer" 3,
          branch "server.version.choose"
            [("none", "server.unsupported"), ("some", "server.version")])
      , (site "UploadServer" 4,
          SourceBranchReceiveFrameNonreturningFallback "server.version")
      , (site "UploadServer" 5,
          branch "server.version"
            [("accepted", "server.begin.commit"),
             ("rejected", "server.begin.recognition_failure")])
      , (site "UploadServer" 6,
          branch "server.begin.commit"
            [("accepted", "server.proceed"), ("rejected", "server.reject")])
      , (site "UploadServer" 7,
          branch "server.proceed"
            [("cancel", "server.cancel"), ("payload", "server.payload")])
      , (site "UploadServer" 8,
          branch "server.payload"
            [("fallback", "server.early_eof"), ("primary", "server.digest")])
      , (site "UploadServer" 9,
          branch "server.digest"
            [("accepted", "server.store"), ("rejected", "server.digest_mismatch")])
      , (site "UploadServer" 10,
          branch "server.store"
            [("failure", "server.storage_failure"), ("success", "server.accepted")])
      ]
  }

-- Steve ------------------------------------------------------------------------

checkedSteveArchitecture :: Text -> Text -> Either String CheckedSourceArchitecture
checkedSteveArchitecture putSource getSource = do
  checked <- mapLeft show $ checkPortableSourceBundle
    steveRoots steveEnvironments (steveBundle putSource getSource)
  mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:steve" (InstanceLineageSiteId "instance.steve"))
    checked

steveBundle :: Text -> Text -> PortableSourceBundle
steveBundle putSource getSource = PortableSourceBundle
  { portableGrammarRevision = canonicalGrammarRevisionV1
  , portableSelectedProgramRoot = "program:steve"
  , portableSourceUnits =
      [ PortableSourceUnit
          (SourceUnitId "unit.steve.put")
          (DeclarationSiteId "site.steve.put")
          (Just "decl:steve.put")
          putSource
      , PortableSourceUnit
          (SourceUnitId "unit.steve.get")
          (DeclarationSiteId "site.steve.get")
          (Just "decl:steve.get")
          getSource
      ]
  , portableInstanceLineage =
      [ PortableInstanceLineage
          (InstanceLineageSiteId "instance.steve")
          "inst:phase1.steve"
      ]
  , portableProcessLineage = []
  }

steveRoots :: SourceRootMap
steveRoots = Map.singleton "program:steve" stevePutDeclaration

stevePutDeclaration, steveGetDeclaration :: DeclarationKey
stevePutDeclaration = DeclarationKey "decl:steve.put"
steveGetDeclaration = DeclarationKey "decl:steve.get"

steveEnvironments :: SourceEnvironmentMap
steveEnvironments = Map.fromList
  [ (stevePutDeclaration, stevePutEnvironment)
  , (steveGetDeclaration, steveGetEnvironment)
  ]

stevePutEnvironment :: SurfaceEnvironment
stevePutEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "candidate"
      (InitialBinding Linear ownedBytesType PlainShape)
  , surfacePrimitives = Map.fromList
      [ ("digest_compute", digestComputePrimitive)
      , ("blob_install", blobInstallPrimitive)
      ]
  , surfaceExpectedProvides = Just TyUnit
  }

steveGetEnvironment :: SurfaceEnvironment
steveGetEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "contentId"
      (InitialBinding Unrestricted contentIdType PlainShape)
  , surfacePrimitives = Map.fromList
      [ ("blob_read", blobReadPrimitive)
      , ("digest_check", digestCheckPrimitive)
      ]
  , surfaceExpectedProvides = Just TyUnit
  , surfaceReleaseTransitions = [ownedBytesRelease]
  }

digestComputePrimitive :: PrimitiveSemantics
digestComputePrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly]
  [ProviderOutcomeSpec "computed" [(Unrestricted, contentIdType)]]

blobInstallPrimitive :: PrimitiveSemantics
blobInstallPrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly, PrimitiveConsume]
  [ ProviderOutcomeSpec "installed" []
  , ProviderOutcomeSpec "already-exists" []
  , ProviderOutcomeSpec "storage-failure" [(Unrestricted, storageFailureType)]
  ]

blobReadPrimitive :: PrimitiveSemantics
blobReadPrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly]
  [ ProviderOutcomeSpec "found" [(Linear, ownedBytesType)]
  , ProviderOutcomeSpec "not-found" []
  , ProviderOutcomeSpec "storage-failure" [(Unrestricted, storageFailureType)]
  ]

digestCheckPrimitive :: PrimitiveSemantics
digestCheckPrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly, PrimitiveReadOnly]
  [ ProviderOutcomeSpec "accepted" []
  , ProviderOutcomeSpec "rejected" [(Unrestricted, digestFailureType)]
  ]

ownedBytesType, contentIdType, storageFailureType, digestFailureType :: Ty
ownedBytesType = TyOpaque "OwnedBytes"
contentIdType = TyOpaque "ContentId[SHA256]"
storageFailureType = TyOpaque "StorageFailure"
digestFailureType = TyOpaque "DigestFailure"

ownedBytesRelease :: ReleaseTransitionContract
ownedBytesRelease = ReleaseTransitionContract
  { releaseTransitionKey = "provider.owned-bytes.release"
  , releaseTransitionOwnerType = ownedBytesType
  , releaseTransitionRequirements = Set.empty
  , releaseTransitionSemanticAccount = ReleaseSemanticAccount
      { releaseAccountAuthorityRefs = Set.empty
      , releaseAccountEvidenceRefs = Set.empty
      , releaseAccountEffectRefs = Set.empty
      , releaseAccountAssumptionRefs = Set.empty
      , releaseAccountCostRefs = Set.empty
      , releaseAccountSubjectRef = "owned-bytes"
      }
  , releaseTransitionOutcome = ReleaseContinuesUnit
  , releaseTransitionResidue = ReleaseConsumesOwner
  }

stevePolicy :: SourceCoreCorrespondencePolicy
stevePolicy = SourceCoreCorrespondencePolicy
  { sourceCoreCallPolicy = Map.fromList
      [ (site "SteveGet" 0, SourceCallRuntimeChoice "BlobProvider.read")
      , (site "SteveGet" 1, SourceCallRuntimeChoice "DigestProvider.check")
      , (site "StevePut" 0, SourceCallRuntimeChoice "DigestProvider.compute")
      , (site "StevePut" 1, SourceCallRuntimeChoice "BlobProvider.install-if-absent")
      ]
  , sourceCoreBranchPolicy = Map.fromList
      [ (site "SteveGet" 0,
          branch "get.entry"
            [("found", "get.check"), ("not-found", "get.not-found"),
             ("storage-failure", "get.failure")])
      , (site "SteveGet" 1,
          branch "get.check"
            [("accepted", "get.ok"), ("rejected", "get.integrity-failure")])
      , (site "StevePut" 0,
          branch "put.entry" [("computed", "put.install")])
      , (site "StevePut" 1,
          branch "put.install"
            [("installed", "put.ok"), ("already-exists", "put.ok"),
             ("storage-failure", "put.failure")])
      ]
  }

site :: Text -> Int -> SourceCoreSite
site = SourceCoreSite

branch :: Text -> [(Text, Text)] -> SourceBranchDisposition
branch blockName targets = SourceBranchDisposition blockName (Map.fromList targets)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
