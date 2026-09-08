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
  )
import Phil.Core.Syntax (Mode (..), Ty (..))
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
