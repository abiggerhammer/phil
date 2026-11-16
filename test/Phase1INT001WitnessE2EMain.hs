{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Compiler.SourceCorePolicy
import Phil.Compiler.SourceSystems
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  , InstanceKey (..)
  , SemanticForm (..)
  )
import Phil.Core.Syntax (Mode (..), Name (..), Proposition (..), Obligation (..), ObligationId (..), Ty (..))
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
import Phil.Surface.Syntax (SourcePoint (..), SourceSpan (..))
import Phil.Systems.GenericLowering
  ( CoreSystemsProgram (..)
  , CoreSystemsBlock (..)
  , CoreSystemsFunction (..)
  , CoreSystemsTerminator (..)
  , GenericRealizationContext (..)
  , GenericLoweringError (..)
  , coreSystemsProgramSemanticForm
  )
import Phil.Systems.Phase1Stage
  ( phase1StageInstanceRevision
  , phase1StageSystemsArtifact
  , verifyPhase1StageBundle
  )
import qualified Phil.Assurance.Types as A
import qualified Phil.Handoff.Phase1AssuranceInputs as H
import Phil.Assurance.Types
  ( ArtifactIdentity (..)
  , AssuranceManifest (..)
  , ArtifactRef (..)
  , AssuranceLedger
  , Digest
  , VerificationContext (..)
  , digestText
  , emptyLedger
  , emptyVerificationContext
  )
import Phil.Core.Generic
  ( GenericStaticParameterKey (..)
  , checkGenericInstantiation
  , deriveGenericApplicationIdentity
  , deriveGenericDischargeLineage
  , strictGenericInstantiationPolicy
  )
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor (..)
  , ArchitectureInstanceIdentity (..)
  , DeclarationIdentity (..)
  , deriveArchitectureInstanceIdentity
  )
import Phil.Systems.ProviderCallCorrespondence (ProviderCallExpectationMap)
import Phil.Systems.RuntimeCarrierBinding
  ( RuntimeCarrierBinding (..), RuntimeCarrierBindingError (..), checkRuntimeCarrierBindings )
import Phil.Systems.RuntimeCarrierCoverage (RuntimeCarrierKey (..))
import Phil.Systems.IR
  ( RuntimeSiteKind (..), RuntimeSiteRef (..)
  , loweringLedgerRoot
  , systemsArtifactDigest
  , systemsArtifactLoweringLedger
  )
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , buildVerificationRevisionGraph
  , buildVerificationObligationGraph
  , VerificationObligationInput (..)
  , VerificationObligationGraph (..)
  , VerificationDisposition (..)
  )
import Phil.Verification.ArtifactClosure
  ( certifyApplicationArtifact )
import Phil.Verification.Bundle
  ( buildVerificationBundle
  , verificationBundleArchitectureDigest
  )
import Phil.Verification.CertifiedRelease
  ( CertifiedReleaseProfile (..)
  , ReleaseProfileRevision (..)
  , ReleaseTrustBoundary (..)
  , ReleaseTrustBoundaryId (..)
  , ReleaseTrustKind (..)
  , certifiedReleaseManifest
  , certifiedReleaseStageClosure
  , certifyReleaseArtifact
  )
import Phil.Verification.GenericAssurance
  ( GenericApplicationAssurance
  , composeGenericApplicationAssurance
  , prepareReusableGenericBodyAssurance
  )
import Phil.Verification.ManifestClosure (ManifestClosureSelection (..))
import Phil.Verification.SourceManifestBinding
  ( CertifiedSourceManifestBinding
  , closeSourceManifestBindingForInstance
  , sourceManifestBindingManifest
  , sourceManifestBindingSourceAssurance
  )
import Phil.Verification.ReleasePackage
  ( buildCertifiedReleasePackage
  , buildStructuralReleasePackage
  , renderStructuralReleasePackage
  , renderCertifiedReleasePackage
  , verifiedOriginPackageStructural
  , certifiedReleasePackageManifestId
  , certifiedReleasePackageLLVMTargetDigest
  )
import Phil.Verification.VerifiedFinalOriginProduction
  ( VerifiedFinalOriginProduction
  , VerifiedFinalOriginError (..)
  , acceptVerifiedFinalOrigin
  , acceptedVerifiedFinalOriginProduction
  , produceVerifiedFinalOrigin
  , verifiedFinalOriginRelease
  , verifiedFinalOriginSourceArtifact
  , verifiedFinalOriginSourceBinding
  , verifiedFinalOriginStageProduction
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
    , test "P9-F2 SteveGet private structural read/borrow/call discriminator"
        (p9SteveStructuralGate stevePut steveGet)
    , test "INT-001 source-owned producer refuses unlisted occurrence site"
        (verifiedProducerRejectsWrongSite uploadClient uploadServer)
    , test "P8-H2 actual Upload P2 rejects malformed realization semantics"
        (p8H2UploadRejectsMalformedContext uploadClient uploadServer)
    , test "P6 Upload whole StageClosure built from sealed ordinary source"
        (uploadVerifiedStageClosure uploadClient uploadServer)
    , test "P6 Steve whole StageClosure built from sealed ordinary source"
        (steveVerifiedStageClosure stevePut steveGet)
    , test "P6 Steve stage config cannot borrow Upload producer"
        (verifiedStageRejectsWrongConcrete uploadClient uploadServer)
    , test "P9-F1 Upload checked source use bound to selected immutable assurance"
        (p9F1Upload uploadClient uploadServer)
    , test "P7 Upload real source-to-final accepting consumer"
        (p7UploadReplay uploadClient uploadServer)
    , test "P7 Steve real source-to-final accepting consumer"
        (p7SteveReplay stevePut steveGet)
    , test "P7 wrong K/source/manifest/stage/release/LLVM/trust are rejected"
        (p7Adversarial uploadClient uploadServer stevePut steveGet)
    , test "P7 Upload origin package requires sealed source/release acceptance"
        (p7OriginPackageReplay (verifiedUploadProduction uploadClient uploadServer)
          uploadProviderCallExpectations uploadStageClosureBundle)
    , test "P7 Steve origin package requires sealed source/release acceptance"
        (p7OriginPackageReplay (verifiedSteveProduction stevePut steveGet)
          steveProviderCallExpectations steveStageClosureBundle)
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
      sourceGraph = verifiedSourceSystemsCheckEventGraph produced
      events = verifiedSourceCheckEventOccurrences sourceGraph
      uploaded = [ checkedEvidenceEvent evidence
                 | evidence <- events
                 , checkedEvidenceUnitId evidence == SourceUnitId "unit.upload.server"
                 , checkedEvidenceDeclarationSite evidence
                     == DeclarationSiteId "site.upload.server" ]
  assert (not (null uploaded))
    "P9-E2 real Upload server lost source-qualified checker uses"
  assert (verifiedSourceCheckEventArchitectureIdentity sourceGraph == occurrence
      && verifiedSourceCheckEventCoreSemantics sourceGraph
           == coreSystemsProgramSemanticForm uploadCoreProgram)
    "P9-E2 private Upload source graph lost exact K/I or admitted Core"
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
      sourceGraph = verifiedSourceSystemsCheckEventGraph produced
  assert (verifiedSourceCheckEventArchitectureIdentity sourceGraph == occurrence
      && verifiedSourceCheckEventCoreSemantics sourceGraph
           == coreSystemsProgramSemanticForm steveCoreProgram)
    "P9-E2 private Steve source graph lost exact K/I or admitted Core"
  mapLeft show (verifyPhase1StageBundle fullStage)
  assert (identityInstanceKey occurrence == InstanceKey "inst:phase1.steve")
    "source-owned producer lost Steve occurrence K"
  assert (identityInstanceRevision occurrence == phase1StageInstanceRevision fullStage)
    "source-owned producer lost Steve occurrence I"
  assert (fullStage == original)
    "source-owned producer changed complete Steve stage"


-- P9-F2 G1 is a bounded structural discriminator only. It does NOT establish
-- the dynamic read owner, live source loan, selected linked ABI or proof.
p9SteveStructuralGate :: Text -> Text -> Either String ()
p9SteveStructuralGate putSource getSource = do
  produced <- verifiedSteveProduction putSource getSource
  _ <- mapLeft show (verifyOriginalSteveGetStructural produced)
  architecture <- checkedSteveArchitecture putSource getSource
  fact <- mapLeft show (verifySteveGetStructural architecture steveCoreProgram)
  assert (steveGetSourceContentBinder fact == "contentId"
      && steveGetSourceOwnerBinder fact == "bytes"
      && steveGetSourceViewBinder fact == "bytesView"
      && steveGetCheckedContentType fact == TyOpaque "ContentId[SHA256]"
      && steveGetCheckedFoundOrdinal fact >= 0
      && steveGetCheckedFoundOrdinal fact < steveGetCheckedCallOrdinal fact)
    "P9 SteveGet real checked found-result / typed-call chain changed"
  let occurrences =
        verifiedSourceCheckEventOccurrences
          (verifiedSourceSystemsCheckEventGraph produced)
      originalFound =
        [ ()
        | occurrence <- occurrences
        , SourceCheckedProviderFound "blob_read" _ (Name "bytes")
            (TyOpaque "OwnedBytes") <-
              [sourceEvidenceUse (checkedEvidenceEvent occurrence)]
        ]
      originalCall =
        [ ()
        | occurrence <- occurrences
        , SourceCheckedProviderCall "digest_check" _ <-
            [sourceEvidenceUse (checkedEvidenceEvent occurrence)]
        ]
  assert (length originalFound == 1 && length originalCall == 1)
    "P9 private P2 graph omitted the real checked provider-result/call events"

  -- The ordinary primitive permits readable arguments without a qualified
  -- expected type vector. The new P9-only discriminator must reject a
  -- genuine source recheck with the WRONG declared content-id type, even
  -- when the source call name, argument names and Core are unchanged.
  let wrongIdEnvironment = Map.adjust
        (\environment -> environment
          { surfaceInitialBindings = Map.insert "contentId"
              (InitialBinding Unrestricted (TyOpaque "WrongContentId") PlainShape)
              (surfaceInitialBindings environment) })
        steveGetDeclaration steveEnvironments
  wronglyTyped <- mapLeft show $ checkPortableSourceBundle
    steveRoots wrongIdEnvironment (steveBundle putSource getSource)
  wrongTypeArchitecture <- mapLeft show $
    buildCheckedSourceArchitecture
      (Map.singleton "program:steve" (InstanceLineageSiteId "instance.steve"))
      wronglyTyped
  case verifySteveGetStructural wrongTypeArchitecture steveCoreProgram of
    Left SteveGetCheckedCallTypeMismatch -> Right ()
    other -> Left
      ("P9 accepted wrongly typed source ContentId: " <> show other)

  let changeTerminator transform core =
        core { coreProgramFunctions =
          Map.adjust
            (\function -> function
              { coreFunctionBlocks =
                  Map.adjust
                    (\block -> block
                      { coreBlockTerminator =
                          transform (coreBlockTerminator block) })
                    "get.check" (coreFunctionBlocks function) })
            "SteveGet" (coreProgramFunctions core)
          }
      swapOperands terminator = case terminator of
        CoreSystemsRuntimeChoice name [first, second] site arms ->
          CoreSystemsRuntimeChoice name [second, first] site arms
        other -> other
      wrongCore = changeTerminator swapOperands steveCoreProgram
  case verifySteveGetStructural architecture wrongCore of
    Left SteveGetCoreDigestSiteMismatch -> Right ()
    other -> Left ("P9 accepted swapped Core arguments: " <> show other)

  let duplicate = steveCoreProgram
        { coreProgramFunctions =
            Map.adjust
              (\function -> function
                { coreFunctionBlocks =
                    Map.insert "get.unrelated-duplicate"
                      (CoreSystemsBlock "get.unrelated-duplicate" []
                        (CoreSystemsRuntimeChoice "DigestProvider.check"
                          ["get.id", "get.bytes-view"] Nothing
                          (Map.fromList
                            [("accepted", "get.ok")
                            ,("rejected", "get.integrity-failure")])))
                      (coreFunctionBlocks function) })
              "SteveGet" (coreProgramFunctions steveCoreProgram)
        }
  case verifySteveGetStructural architecture duplicate of
    Left SteveGetCoreDigestNotUnique -> Right ()
    other -> Left ("P9 accepted duplicate Core digest-check site: " <> show other)

  let swappedSource = Text.replace
        "digest_check(contentId, bytesView)"
        "digest_check(bytesView, contentId)" getSource
  assert (swappedSource /= getSource)
    "P9 source operand negative did not change source text"
  swappedArchitecture <- checkedSteveArchitecture putSource swappedSource
  case verifySteveGetStructural swappedArchitecture steveCoreProgram of
    Left SteveGetDigestOperandsMismatch -> Right ()
    other -> Left ("P9 accepted swapped source digest operands: " <> show other)

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

-- Real source-path regression for the H1 native witness. Unlike the public
-- generic/diagnostic controls, this must reject at P2 before sealing a stage.
p8H2UploadRejectsMalformedContext :: Text -> Text -> Either String ()
p8H2UploadRejectsMalformedContext clientSource serverSource = do
  _ <- verifiedUploadProduction clientSource serverSource
  clientEnvironment <- mapLeft show (phase0EnvironmentFor "client.phil")
  serverEnvironment <- mapLeft show (phase0EnvironmentFor "server.phil")
  let bad = SemanticUnordered (Set.fromDistinctAscList
        [SemanticRecord Map.empty, SemanticUnordered Set.empty])
      context = uploadRealizationContext { genericContextSemantics = bad }
      result = produceVerifiedSourceSystems
        uploadRoots
        (Map.fromList
          [ (uploadClientDeclaration, clientEnvironment)
          , (uploadServerDeclaration, serverEnvironment) ])
        (Map.singleton "program:upload" (InstanceLineageSiteId "instance.upload"))
        uploadPolicy (uploadBundle clientSource serverSource)
        uploadCoreProgram context
  case result of
    Left (VerifiedSourceLoweringRejected
      (SourceSystemsLoweringRejected GenericLoweringMalformedContextSemantics)) ->
        Right ()
    other -> Left ("malformed Upload context crossed P2: " <> show other)

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
  assert (verifiedStageClosureSourceCheckEventGraph retained
      == verifiedSourceSystemsCheckEventGraph production)
    "P9-E2 Upload P6 changed its exact P2 source-checker events"
  assertStageFromProduction production (verifiedStageClosureSelected retained)

steveVerifiedStageClosure :: Text -> Text -> Either String ()
steveVerifiedStageClosure putSource getSource = do
  production <- verifiedSteveProduction putSource getSource
  template <- steveStageClosureBundle
  retained <- mapLeft show
    (produceVerifiedStageClosure production steveProviderCallExpectations template)
  assert (verifiedStageClosureSourceProduction retained == production)
    "Steve lost sealed producer"
  assert (verifiedStageClosureSourceCheckEventGraph retained
      == verifiedSourceSystemsCheckEventGraph production)
    "P9-E2 Steve P6 changed its exact P2 source-checker events"
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


-- P7: the first final-origin positive fixture starts with ordinary PHIL text,
-- not the independent generic-source/StageClosure fixtures in INT-005.
data P7Fixture = P7Fixture
  { p7Production :: VerifiedFinalOriginProduction
  , p7Context :: VerificationContext
  , p7Ledger :: AssuranceLedger
  , p7Profile :: CertifiedReleaseProfile
  , p7LLVM :: LLVMArtifact
  , p7Trust :: [ReleaseTrustBoundary]
  }

p7UploadReplay :: Text -> Text -> Either String ()
p7UploadReplay clientSource serverSource = do
  prod <- verifiedUploadProduction clientSource serverSource
  template <- uploadStageClosureBundle
  fixture <- makeP7Fixture prod uploadProviderCallExpectations template
  p7AcceptsExact fixture

p7SteveReplay :: Text -> Text -> Either String ()
p7SteveReplay putSource getSource = do
  prod <- verifiedSteveProduction putSource getSource
  template <- steveStageClosureBundle
  fixture <- makeP7Fixture prod steveProviderCallExpectations template
  p7AcceptsExact fixture

p7AcceptsExact :: P7Fixture -> Either String ()
p7AcceptsExact fixture = do
  let produced = p7Production fixture
  accepted <- mapLeft show (acceptVerifiedFinalOrigin produced
    (verifiedFinalOriginSourceBinding produced)
    (verifiedFinalOriginSourceArtifact produced)
    (verifiedFinalOriginRelease produced))
  assert (acceptedVerifiedFinalOriginProduction accepted == produced)
    "final-origin accepted result lost the exact source/manifest/stage/release"

makeP7Fixture
  :: VerifiedSourceSystemsProduction
  -> ProviderCallExpectationMap
  -> StageClosureBundle
  -> Either String P7Fixture
makeP7Fixture prod expectations template = do
  stageProd <- mapLeft show (produceVerifiedStageClosure prod expectations template)
  let stage = verifiedStageClosureSelected stageProd
      descriptor = verifiedSourceSystemsArchitectureDescriptor prod
      systems = phase1StageSystemsArtifact (verifiedSourceSystemsStage prod)
      llvm = lowerSystemsConservative phase0LLVMTarget systems
  source <- makeP7Source descriptor (ArtifactRef "p7.ordinary-source-proof")
  (binding, context) <- makeP7Binding source descriptor stage
    (digestText "p7.accepted.phil-core")
  let profile = CertifiedReleaseProfile
        { releaseProfileRevision = ReleaseProfileRevision "p7.conventional.v1"
        , releaseProfileManifestTarget = "phase1-p7-conventional"
        , releaseProfileManifestCompilationProfile = "phase1-p7-checked"
        , releaseProfileLLVMTarget = phase0LLVMTarget
        , releaseProfileRequiredTrustKinds = Set.fromList
            [ CompilerCheckerTrust, LLVMToolchainTrust, RuntimeTrust
            , ProviderTrust, ExternalCheckerTrust, TargetAssumptionTrust ]
        }
      trust =
        [ p7TrustValue "compiler" CompilerCheckerTrust
        , p7TrustValue "llvm" LLVMToolchainTrust
        , p7TrustValue "runtime" RuntimeTrust
        , p7TrustValue "provider" ProviderTrust
        , p7TrustValue "checker" ExternalCheckerTrust
        , p7TrustValue "target" TargetAssumptionTrust ]
      ledger = emptyLedger
  result <- mapLeft show
    (produceVerifiedFinalOrigin stageProd binding context ledger profile llvm trust)
  assert (certifiedReleaseStageClosure (verifiedFinalOriginRelease result) == stage)
    "P7 changed the complete P6-produced StageClosure"
  assert (certifiedReleaseManifest (verifiedFinalOriginRelease result)
    == sourceManifestBindingManifest binding)
    "P7 changed the complete checked source manifest"
  pure (P7Fixture result context ledger profile llvm trust)

p7TrustValue :: Text -> ReleaseTrustKind -> ReleaseTrustBoundary
p7TrustValue name kind = ReleaseTrustBoundary
  { releaseTrustBoundaryId = ReleaseTrustBoundaryId name
  , releaseTrustKind = kind
  , releaseTrustName = name
  , releaseTrustRevision = "p7.trust.v1"
  , releaseTrustBasis = "existing Phase 1 declared TCB"
  }

makeP7Source
  :: ArchitectureInstanceDescriptor
  -> ArtifactRef
  -> Either String GenericApplicationAssurance
makeP7Source descriptor evidenceRef = do
  let declaration = architectureDeclarationIdentity descriptor
      key = identityDeclarationKey declaration
      interface = identityInterfaceRevision declaration
      definition = identityDefinitionRevision declaration
      actuals =
        [ (GenericStaticParameterKey k, value)
        | (k, value) <- Map.toAscList (architectureStaticBindings descriptor) ]
  body <- mapLeft show (prepareReusableGenericBodyAssurance
    key interface definition Set.empty
    (ArtifactIdentity evidenceRef (digestText "p7.checked.body-evidence")))
  application <- mapLeft show (deriveGenericApplicationIdentity key interface actuals)
  disposition <- mapLeft show (checkGenericInstantiation
    strictGenericInstantiationPolicy Set.empty [])
  mapLeft show (composeGenericApplicationAssurance body Set.empty
    (deriveGenericDischargeLineage application definition disposition))

makeP7Binding
  :: GenericApplicationAssurance
  -> ArchitectureInstanceDescriptor
  -> StageClosureBundle
  -> Digest
  -> Either String (CertifiedSourceManifestBinding, VerificationContext)
makeP7Binding source descriptor stage coreDigest = do
  graph <- mapLeft show (buildVerificationRevisionGraph [] Set.empty)
  let policy = ApplicationAssurancePolicy
        (AssurancePolicyRevision "p7.source-manifest.v1") Set.empty
  bundle <- mapLeft show (buildVerificationBundle
    (digestText "p7.verified-ordinary-source-revision")
    [architectureDeclarationIdentity descriptor]
    [deriveArchitectureInstanceIdentity descriptor] [] graph policy [])
  let systems = phase1StageSystemsArtifact
        (subjectStageBase (concreteSubjectStage (stageClosureConcrete stage)))
      context = emptyVerificationContext
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationPhilCoreDigest = coreDigest
        , verificationImplementationDigest = systemsArtifactDigest systems
        , verificationTarget = "phase1-p7-conventional"
        , verificationCompilationProfile = "phase1-p7-checked"
        , verificationLoweringLedgerRoot =
            loweringLedgerRoot (systemsArtifactLoweringLedger systems)
        }
      selection = ManifestClosureSelection
        Set.empty Set.empty Map.empty Set.empty
  binding <- mapLeft show (closeSourceManifestBindingForInstance
    source descriptor bundle policy context emptyLedger selection)
  pure (binding, context)

-- The actual package consumer accepts only the P2/P6/P7-sealed final event.
-- Direct entry with a legacy release is a separate compile-negative control.
p7OriginPackageReplay
  :: Either String VerifiedSourceSystemsProduction
  -> ProviderCallExpectationMap
  -> Either String StageClosureBundle -> Either String ()
p7OriginPackageReplay productionResult expectations templateResult = do
  production <- productionResult
  template <- templateResult
  fixture <- makeP7Fixture production expectations template
  let seal = p7Production fixture
      release = verifiedFinalOriginRelease seal
  accepted <- mapLeft show (acceptVerifiedFinalOrigin seal
    (verifiedFinalOriginSourceBinding seal)
    (verifiedFinalOriginSourceArtifact seal) release)
  package <- mapLeft show (buildCertifiedReleasePackage (p7Ledger fixture) accepted)
  let structural = verifiedOriginPackageStructural package
      rendered = renderCertifiedReleasePackage package
      occurrence = verifiedSourceSystemsArchitectureIdentity production
      key = unInstanceKey (identityInstanceKey occurrence)
  assert (certifiedReleasePackageManifestId structural
      == manifestId (certifiedReleaseManifest release))
    "verified package lost independently accepted manifest"
  assert (certifiedReleasePackageLLVMTargetDigest structural
      == llvmContractTargetDigest (llvmArtifactContract (p7LLVM fixture)))
    "verified package lost accepted LLVM target"
  assert (Text.isInfixOf ("verified-origin\tinstance-key=" <> key) rendered)
    "verified package renderer lost exact checked K"
  assert (Text.isInfixOf "instance-revision=" rendered
    && Text.isInfixOf "package-id=" rendered)
    "verified package renderer lost checked I and package identity"

-- Each negative is rejected by the mandatory P7 accepting consumer; earlier
-- structural constructors alone never return the stronger accepted-origin type.
p7Adversarial :: Text -> Text -> Text -> Text -> Either String ()
p7Adversarial clientSource serverSource putSource getSource = do
  uploadProd <- verifiedUploadProduction clientSource serverSource
  uploadTemplate <- uploadStageClosureBundle
  upload <- makeP7Fixture uploadProd uploadProviderCallExpectations uploadTemplate
  steveProd <- verifiedSteveProduction putSource getSource
  steveTemplate <- steveStageClosureBundle
  steve <- makeP7Fixture steveProd steveProviderCallExpectations steveTemplate
  let seal = p7Production upload
      binding = verifiedFinalOriginSourceBinding seal
      artifact = verifiedFinalOriginSourceArtifact seal
      release = verifiedFinalOriginRelease seal
      stageProd = verifiedFinalOriginStageProduction seal
      selected = verifiedStageClosureSelected stageProd
      descriptor = verifiedSourceSystemsArchitectureDescriptor uploadProd
      source = sourceManifestBindingSourceAssurance binding
      check candidateBinding candidateSource candidateRelease expected =
        case acceptVerifiedFinalOrigin seal candidateBinding candidateSource candidateRelease of
          Left actual | actual == expected -> Right ()
          result -> Left ("wrong P7 rejection: " <> show result)
  p7AcceptsExact upload
  p7AcceptsExact steve
  -- A public identity record CAN reuse I with a different K, but it is not
  -- an admissible opaque P2/P6 producer or source-manifest certificate.
  let actualIdentity = verifiedSourceSystemsArchitectureIdentity uploadProd
      forgedSameI = ArchitectureInstanceIdentity
        (InstanceKey "forged.other-occurrence-key")
        (identityInstanceRevision actualIdentity)
  assert (identityInstanceRevision forgedSameI == identityInstanceRevision actualIdentity
       && identityInstanceKey forgedSameI /= identityInstanceKey actualIdentity)
    "P7 same-I/different-K adversarial identity was not distinct"
  let otherKey = descriptor
        { architectureInstanceKey = identityInstanceKey forgedSameI }
  (wrongKeyBinding, _) <- makeP7Binding source otherKey selected
    (digestText "p7.accepted.phil-core")
  assert (otherKey /= descriptor) "P7 K swap was not distinct"
  case produceVerifiedFinalOrigin stageProd wrongKeyBinding
      (p7Context upload) (p7Ledger upload) (p7Profile upload)
      (p7LLVM upload) (p7Trust upload) of
    Left VerifiedFinalOriginSourceOccurrenceMismatch -> Right ()
    other -> Left ("P7 wrong K got: " <> show other)
  check wrongKeyBinding artifact release VerifiedFinalOriginSourceBindingSubstituted
  otherSource <- makeP7Source descriptor (ArtifactRef "p7.substituted-proof")
  otherArtifact <- mapLeft show (certifyApplicationArtifact otherSource selected)
  check binding otherArtifact release VerifiedFinalOriginCertifiedSourceSubstituted
  (otherBinding, _) <- makeP7Binding source descriptor selected
    (digestText "p7.changed.phil-core")
  assert (otherBinding /= binding) "P7 manifest substitution was not distinct"
  check otherBinding artifact release VerifiedFinalOriginSourceBindingSubstituted
  oldStageArtifact <- mapLeft show (certifyApplicationArtifact source uploadTemplate)
  assert (oldStageArtifact /= artifact) "P7 independently built stage was not distinct"
  check binding oldStageArtifact release VerifiedFinalOriginCertifiedSourceSubstituted
  check binding artifact (verifiedFinalOriginRelease (p7Production steve))
    VerifiedFinalOriginCertifiedReleaseSubstituted
  let alteredTrust = case p7Trust upload of
        [] -> []
        (first : rest) -> first { releaseTrustBasis = "changed accepted trust" } : rest
  alternateTrustRelease <- mapLeft show (certifyReleaseArtifact
    (p7Profile upload) (p7Context upload) (p7Ledger upload)
    (sourceManifestBindingManifest binding) selected (p7LLVM upload) alteredTrust)
  assert (alternateTrustRelease /= release) "P7 trust substitution was not distinct"
  check binding artifact alternateTrustRelease VerifiedFinalOriginCertifiedReleaseSubstituted
  let alternateTarget = phase0LLVMTarget
        { llvmTargetTripleName = "aarch64-unknown-linux-gnu" }
      alternateProfile = (p7Profile upload)
        { releaseProfileLLVMTarget = alternateTarget }
      alternateLLVM = lowerSystemsConservative alternateTarget
        (phase1StageSystemsArtifact (verifiedSourceSystemsStage uploadProd))
  alternateLLVMRelease <- mapLeft show (certifyReleaseArtifact
    alternateProfile (p7Context upload) (p7Ledger upload)
    (sourceManifestBindingManifest binding) selected alternateLLVM (p7Trust upload))
  assert (alternateLLVMRelease /= release) "P7 LLVM substitution was not distinct"
  check binding artifact alternateLLVMRelease VerifiedFinalOriginCertifiedReleaseSubstituted

-- This is a source-derived P2/P6 and selected-immutable-use test, NOT P7 final
-- consumption. Even completely rehashed caller-selected ledger data cannot
-- substitute a distinct original site in the sealed checker graph.
p9F1Upload :: Text -> Text -> Either String ()
p9F1Upload clientSource serverSource = do
  production <- verifiedUploadProduction clientSource serverSource
  template <- uploadStageClosureBundle
  stage <- mapLeft show
    (produceVerifiedStageClosure production uploadProviderCallExpectations template)
  let sourceGraph = verifiedStageClosureSourceCheckEventGraph stage
      instanceId = verifiedSourceCheckEventArchitectureIdentity sourceGraph
      qualified = [ (occurrence, proposition, name)
        | occurrence <- verifiedSourceCheckEventOccurrences sourceGraph
        , SourceRequirementEvidence proposition (Just name) Nothing <-
            [sourceEvidenceUse (checkedEvidenceEvent occurrence)]
        , name == Name "beginPolicy" ]
  (occurrence, proposition, binder) <- case qualified of
    (oneProof : _) -> Right oneProof
    [] -> Left "P9-F1 actual Upload proof consumer missing"
  let event = checkedEvidenceEvent occurrence
      fact = A.StaticCheckedSourceFact
        { A.staticUseSourceUnit = checkedEvidenceUnitId occurrence
        , A.staticUseDeclarationSite = checkedEvidenceDeclarationSite occurrence
        , A.staticUseDeclarationKey = checkedEvidenceDeclarationKey occurrence
        , A.staticUseArchitecture = instanceId
        , A.staticUseSite = sourceEvidenceSite event
        , A.staticUseBranches = sourceEvidenceBranchRoute event
        , A.staticUseOrdinal = sourceEvidenceOrdinal event
        , A.staticUseOriginalProposition = proposition
        , A.staticUseCanonicalProposition = proposition
        , A.staticUseKind = A.StaticRequirementByBinding binder }
  assert (not (null (A.staticUseBranches fact)))
    "P9-F1 selected Upload policy proof has no checked branch"
  (binding, context, ledger, useId) <- p9F1Selection production fact
  _ <- mapLeft show
    (acceptSelectedCheckedStaticUse stage binding context ledger useId)
  -- The typed immutable handoff is a reversible schema, not a copied
  -- authority token. Deliberately mutate the actual nested typed source fact.
  let selectedIds = Map.keysSet (A.ledgerEvidence ledger)
      p9Selection = ManifestClosureSelection
        selectedIds Set.empty Map.empty (Set.singleton useId)
      p9Policy = ApplicationAssurancePolicy
        (AssurancePolicyRevision "p9.f1.handoff.v1")
        (Set.singleton StaticallyDischarged)
  inputs <- mapLeft show
    (H.derivePhase1AssuranceInputs p9Policy ledger p9Selection)
  let staticWire = H.renderPhase1AssuranceInputs inputs
  decoded <- mapLeft show (H.decodePhase1AssuranceInputs staticWire)
  assert (decoded == inputs) "P9-F1 typed static-use handoff round-trip changed fact"
  assert ("use-static-v1\t" `Text.isInfixOf` staticWire)
    "P9-F1 typed handoff lost static use variant"
  let variantsWire =
        [ ("unknown static use revision",
           Text.replace "use-static-v1\t" "use-static-v2\t" staticWire)
        , ("truncated checked-source-fact field",
           Text.unlines (map truncateStaticFact (Text.lines staticWire)))
        , ("deceptively encoded use variant",
           Text.replace "use-static-v1\t" "use-runtime\t" staticWire)
        ]
      truncateStaticFact wireLine
        | "use-static-v1\t" `Text.isPrefixOf` wireLine =
            case Text.splitOn "\t" wireLine of
              [tag, key, digest, revision, entries, factHex] ->
                Text.intercalate "\t" [tag, key, digest, revision, entries,
                  Text.dropEnd 2 factHex]
              _ -> wireLine
        | otherwise = wireLine
  mapM_ (\(label, wire) -> case H.decodePhase1AssuranceInputs wire of
    Left _ -> Right ()
    Right _ -> Left ("P9-F1 decoded altered static handoff: " ++ label))
    variantsWire
  -- Loss of the entire use row is distinguishable from the original selected
  -- manifest; a standalone empty selection remains valid for weaker APIs.
  let missingUseWire = Text.unlines
        (filter (not . Text.isPrefixOf "use-static-v1\t") (Text.lines staticWire))
  lostInput <- mapLeft show (H.decodePhase1AssuranceInputs missingUseWire)
  assert (lostInput /= inputs)
    "P9-F1 missing selected use row silently matched original selection"
  -- Only retained-runtime uses belong in runtime-carrier binding. Even a
  -- manifest-selected checked-static use cannot acquire one via a fake site.
  let staticManifest = sourceManifestBindingManifest binding
      staticSystems = phase1StageSystemsArtifact
        (verifiedSourceSystemsStage (verifiedStageClosureSourceProduction stage))
      selectedEvidence = head (Map.elems (A.ledgerEvidence ledger))
      fakeSite = RuntimeSiteRef
        (SourceSemanticRuntime "p9.f1.not-a-runtime-site")
        (A.evidenceObligationRevision selectedEvidence)
        (A.evidenceEntryId selectedEvidence)
        "p9.f1.forged-cost"
      fakeBinding = RuntimeCarrierBinding useId
        (RuntimeCarrierKey "p9.f1.forged-carrier") fakeSite
  mapLeft show (checkRuntimeCarrierBindings ledger staticManifest staticSystems
    Map.empty Map.empty)
  -- INT-005 structural output must identify the selected checked-static fact
  -- separately, without claiming that the final P7 consumer used it.
  let p9LLVM = lowerSystemsConservative phase0LLVMTarget staticSystems
      p9Trust = [p7TrustValue "compiler" CompilerCheckerTrust]
      p9Profile = CertifiedReleaseProfile
        { releaseProfileRevision = ReleaseProfileRevision "p9.f1.static.trace.v1"
        , releaseProfileManifestTarget = "p9-f1-source-target"
        , releaseProfileManifestCompilationProfile = "p9-f1-checked"
        , releaseProfileLLVMTarget = phase0LLVMTarget
        , releaseProfileRequiredTrustKinds = Set.singleton CompilerCheckerTrust
        }
  release <- mapLeft show (certifyReleaseArtifact
    p9Profile context ledger staticManifest (verifiedStageClosureSelected stage)
    p9LLVM p9Trust)
  package <- mapLeft show (buildStructuralReleasePackage ledger release)
  let packageTrace = renderStructuralReleasePackage package
  assert ("kind=checked-static-v1" `Text.isInfixOf` packageTrace)
    "P9-F1 release sidecar lost distinct static-use type"
  assert (("fact-digest=" <> A.unDigest (A.deriveStaticCheckedSourceFactDigest fact))
      `Text.isInfixOf` packageTrace)
    "P9-F1 release sidecar lost selected typed source-fact digest"
  assert (("evidence=" <> A.unEvidenceEntryId
      (A.evidenceEntryId selectedEvidence)) `Text.isInfixOf` packageTrace)
    "P9-F1 release sidecar lost selected immutable evidence"
  case checkRuntimeCarrierBindings ledger staticManifest staticSystems
      Map.empty (Map.singleton useId fakeBinding) of
    Left (RuntimeCarrierBindingDomainMismatch expected actual)
      | Set.null expected && actual == Set.singleton useId -> Right ()
    other -> Left ("P9-F1 static-use runtime carrier spoof: " ++ show other)
  -- The substituted fully rehashed selection passes ordinary immutable
  -- closure, but MUST be rejected at the real sealed source event consumer.
  let wrongFact = fact { A.staticUseOrdinal = A.staticUseOrdinal fact + 42 }
      originalPoint = sourceSpanStart (A.staticUseSite fact)
      changedPoint = originalPoint
        { sourcePointOffset = sourcePointOffset originalPoint + 1 }
      changedSpan = (A.staticUseSite fact)
        { sourceSpanStart = changedPoint }
      originalArch = A.staticUseArchitecture fact
      fakeArch = originalArch { identityInstanceKey = InstanceKey "inst:forged-same-I" }
      variants =
        [ ("ordinal", wrongFact)
        , ("source unit", fact { A.staticUseSourceUnit = SourceUnitId "unit.forged" })
        , ("declaration site", fact
            { A.staticUseDeclarationSite = DeclarationSiteId "site.forged" })
        , ("source span", fact { A.staticUseSite = changedSpan })
        , ("branch", fact { A.staticUseBranches = [] })
        , ("same I wrong K", fact { A.staticUseArchitecture = fakeArch })
        , ("semantic subject", fact
            { A.staticUseOriginalProposition = Negation proposition
            , A.staticUseCanonicalProposition = Negation proposition })
        ]
  mapM_ (rejectForged stage production) variants
  emptySource <- makeP7Source
    (verifiedSourceSystemsArchitectureDescriptor production)
    (A.ArtifactRef "p9.f1.empty-source")
  let descriptor = verifiedSourceSystemsArchitectureDescriptor production
  (emptyBinding, emptyContext) <- makeP7Binding emptySource descriptor
    (verifiedStageClosureSelected stage) (A.digestText "p9.f1.empty-core")
  case acceptSelectedCheckedStaticUse
      stage emptyBinding emptyContext A.emptyLedger useId of
    Left (StaticUseNotSelected _) -> Right ()
    other -> Left ("P9-F1 empty manifest credited proof: " ++ show other)

rejectForged
  :: VerifiedStageClosureProduction
  -> VerifiedSourceSystemsProduction
  -> (String, A.StaticCheckedSourceFact)
  -> Either String ()
rejectForged stage production (label, fact) = do
  (wrongBinding, wrongContext, wrongLedger, wrongId) <-
    p9F1Selection production fact
  case acceptSelectedCheckedStaticUse stage
      wrongBinding wrongContext wrongLedger wrongId of
    Left (StaticUseNotObservedByOriginalChecker _) -> Right ()
    other -> Left ("P9-F1 forged " ++ label ++ " accepted: " ++ show other)

p9F1Selection
  :: VerifiedSourceSystemsProduction
  -> A.StaticCheckedSourceFact
  -> Either String
       (CertifiedSourceManifestBinding, A.VerificationContext,
        A.AssuranceLedger, A.AssuranceUseId)
p9F1Selection production fact = do
  let descriptor = verifiedSourceSystemsArchitectureDescriptor production
      proposition = A.staticUseCanonicalProposition fact
      obligationKey = ObligationId "p9.f1.upload.checked-policy"
      evidenceKey = A.EvidenceEntryId "p9.f1.upload.source-evidence"
      useKey = A.AssuranceUseId "p9.f1.upload.checked-static-use"
      policy = ApplicationAssurancePolicy
        (AssurancePolicyRevision "p9.f1.checked-static.v1")
        (Set.singleton StaticallyDischarged)
      input = VerificationObligationInput
        { verificationInputObligation = Obligation
            { obligationId = obligationKey
            , obligationProposition = proposition
            , obligationOrigin = "P9-F1 exact Upload source proof use"
            , obligationScope = "upload.checked.policy"
            , obligationRequiredPoint = "original static checker" }
        , verificationInputKind = "checked-source-proof-use"
        , verificationInputRepresentation = "P9-F1 sealed source fact"
        , verificationInputSubjectIds = []
        , verificationInputContextIds = []
        , verificationInputAcceptanceRule =
            A.AcceptEntry A.KernelChecked (A.EvidenceRole "source_checked_static_use")
        , verificationInputDependencies = Set.empty }
  graph <- mapLeft show (buildVerificationObligationGraph
    [input] (Set.singleton obligationKey))
  revision <- case Map.elems (verificationGraphNodes graph) of
    [oneRevision] -> Right oneRevision
    _ -> Left "P9-F1 expected exactly one selected revision"
  let rawEvidence = A.EvidenceEntry
        { A.evidenceEntryId = evidenceKey
        , A.evidenceEntryDigest = A.Digest ""
        , A.evidenceObligationRevision = A.revisionId revision
        , A.evidenceAssuranceKind = A.KernelChecked
        , A.evidenceRole = A.EvidenceRole "source_checked_static_use"
        , A.evidenceProducer = "Phil.Surface.Check.Engine"
        , A.evidenceChecker = "Phil.Surface.Check.Engine"
        , A.evidenceArtifact = Nothing
        , A.evidenceInputDigests = [A.deriveStaticCheckedSourceFactDigest fact]
        , A.evidenceAssumptions = []
        , A.evidenceDependsOn = []
        , A.evidenceValidityScope = A.ValidityScope Map.empty
        , A.evidenceResult = A.EvidenceAccepted
        , A.evidenceJustifies = [A.renderPropositionCanonical proposition]
        , A.evidenceRuntimeMechanism = Nothing
        , A.evidenceRuntimeResidue = []
        , A.evidenceCostRefs = [] }
      evidence = rawEvidence
        { A.evidenceEntryDigest = A.deriveEvidenceEntryDigest rawEvidence }
      rawUse = A.CheckedStaticUse
        { A.assuranceUseId = useKey
        , A.assuranceUseDigest = A.Digest ""
        , A.useObligationRevision = A.revisionId revision
        , A.useEvidenceEntries = [evidenceKey]
        , A.useCheckedStaticFact = fact }
      selectedUse = rawUse
        { A.assuranceUseDigest = A.deriveAssuranceUseDigest rawUse }
      ledger = A.emptyLedger
        { A.ledgerRevisions = verificationGraphNodes graph
        , A.ledgerEvidence = Map.singleton evidenceKey evidence
        , A.ledgerUses = Map.singleton useKey selectedUse }
  bundle <- mapLeft show (buildVerificationBundle
    (A.digestText "p9.f1.checked-source-revision")
    [architectureDeclarationIdentity descriptor]
    [deriveArchitectureInstanceIdentity descriptor] []
    graph policy [evidence])
  let producedSystems = phase1StageSystemsArtifact
        (verifiedSourceSystemsStage production)
      context = A.emptyVerificationContext
        { A.verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , A.verificationPhilCoreDigest = A.digestText "p9.f1.checked-core"
        , A.verificationImplementationDigest = systemsArtifactDigest producedSystems
        , A.verificationTarget = "p9-f1-source-target"
        , A.verificationCompilationProfile = "p9-f1-checked"
        , A.verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        , A.verificationLoweringLedgerRoot = loweringLedgerRoot
            (systemsArtifactLoweringLedger producedSystems) }
      selection = ManifestClosureSelection
        (Set.singleton evidenceKey) Set.empty Map.empty (Set.singleton useKey)
  source <- makeP7Source descriptor (A.ArtifactRef "p9.f1.real-source-body")
  binding <- mapLeft show (closeSourceManifestBindingForInstance
    source descriptor bundle policy context ledger selection)
  pure (binding, context, ledger, useKey)
