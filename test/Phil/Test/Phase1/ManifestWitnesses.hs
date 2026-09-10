{-# LANGUAGE OverloadedStrings #-}

module Phil.Test.Phase1.ManifestWitnesses
  ( RealManifestFixture (..)
  , uploadRealManifestFixture
  , steveRealManifestFixture
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Phase0
  ( phase0UploadLedger
  , phase0UploadManifest
  , phase0UploadVerificationContext
  )
import Phil.Assurance.Types
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.Static
  ( ArchitectureInstanceIdentity (..)
  , CheckedArchitectureInstance (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , InterfaceRevision (..)
  , SemanticForm
  , canonicalSemanticForm
  , deriveDeclarationIdentity
  , emptyStaticContext
  )
import Phil.Core.Syntax (Mode (..), ObligationId (..), Ty (..))
import Phil.Examples.Phase1.StageClosureWitnesses
  ( steveStageClosureBundle
  , uploadStageClosureBundle
  )
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveCoreProgram
  , uploadCoreProgram
  )
import Phil.Examples.Steve.ProviderQualifications
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
import Phil.Surface.Syntax (Located (..))
import Phil.Systems.GenericLowering (coreSystemsProgramSemanticForm)
import Phil.Systems.IR
  ( SystemsArtifact
  , loweringLedgerRoot
  , systemsArtifactDigest
  , systemsArtifactLoweringLedger
  )
import Phil.Systems.Phase1Stage (phase1StageSystemsArtifact)
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , concreteSubjectStage
  , verifyStageClosureBundle
  )
import Phil.Systems.SubjectCorrespondence (SubjectStageBundle (..))
import Phil.Verification
import Phil.Verification.Bundle
import Phil.Verification.ManifestClosure

data RealManifestFixture = RealManifestFixture
  { realFixtureContext :: VerificationContext
  , realFixtureLedger :: AssuranceLedger
  , realFixtureManifest :: AssuranceManifest
  , realFixtureStage :: StageClosureBundle
  } deriving (Eq, Show)

uploadRealManifestFixture :: Text -> Text -> Either String RealManifestFixture
uploadRealManifestFixture clientSource serverSource = do
  architecture <- checkedUploadArchitecture clientSource serverSource
  stage <- uploadStageClosureBundle
  mapLeft show (verifyStageClosureBundle stage)
  graph <- mapLeft show $ buildVerificationRevisionGraph
    (Map.elems (ledgerRevisions phase0UploadLedger))
    (manifestCertificationScope phase0UploadManifest)
  let declarations = map sourceDeclarationIdentity
        (checkedSourceUnits (checkedSourceArchitectureBundle architecture))
      architectureIdentity = checkedArchitectureIdentity
        (checkedSourceArchitectureRoot architecture)
      sourceRevision = deriveSourceRevision "phase1-int002-upload-source-v1"
        declarations architectureIdentity
  bundle <- mapLeft show $ buildVerificationBundle
    sourceRevision declarations [architectureIdentity] [] graph
    uploadAssurancePolicy (Map.elems (ledgerEvidence phase0UploadLedger))
  let systems = stageSystemsArtifact stage
      context = phase0UploadVerificationContext
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationPhilCoreDigest = digestText
            (canonicalSemanticForm (coreSystemsProgramSemanticForm uploadCoreProgram))
        , verificationImplementationDigest = systemsArtifactDigest systems
        , verificationTarget = "phase1-upload"
        , verificationCompilationProfile = "phase1/int002/certified-release"
        , verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        , verificationLoweringLedgerRoot = loweringLedgerRoot
            (systemsArtifactLoweringLedger systems)
        }
      selection = ManifestClosureSelection
        { manifestClosureEvidence = manifestEvidenceEntries phase0UploadManifest
        , manifestClosureAssumptions = manifestAssumptionNodes phase0UploadManifest
        , manifestClosureExports = Map.fromSet (const Exported)
            (manifestExports phase0UploadManifest)
        , manifestClosureUses = manifestAssuranceUses phase0UploadManifest
        }
  manifest <- mapLeft show $ closeVerificationBundle bundle uploadAssurancePolicy
    context phase0UploadLedger selection
  Right RealManifestFixture
    { realFixtureContext = context
    , realFixtureLedger = phase0UploadLedger
    , realFixtureManifest = manifest
    , realFixtureStage = stage
    }

steveRealManifestFixture :: Text -> Text -> Either String RealManifestFixture
steveRealManifestFixture putSource getSource = do
  architecture <- checkedSteveArchitecture putSource getSource
  qualifications <- mapLeft (show . unSteveProviderQualificationError)
    materializeSteveProviderQualifications
  stage <- steveStageClosureBundle
  mapLeft show (verifyStageClosureBundle stage)
  let digestArtifact = steveDigestProviderQualification qualifications
      blobArtifact = steveBlobProviderQualification qualifications
      validity = steveValidityContext digestArtifact blobArtifact
      digestEntries = providerLedgerEntries validity digestArtifact
      blobEntries = providerLedgerEntries validity blobArtifact
  (ledger, evidenceIds, assumptionIds) <- mergeProviderLedgerEntries digestEntries blobEntries
  graph <- mapLeft show $ buildVerificationRevisionGraph
    (Map.elems (ledgerRevisions ledger)) (Map.keysSet (ledgerRevisions ledger))
  let declarations = map sourceDeclarationIdentity
        (checkedSourceUnits (checkedSourceArchitectureBundle architecture))
      architectureIdentity = checkedArchitectureIdentity
        (checkedSourceArchitectureRoot architecture)
      sourceRevision = deriveSourceRevision "phase1-int002-steve-source-v1"
        declarations architectureIdentity
  bundle <- mapLeft show $ buildVerificationBundle
    sourceRevision declarations [architectureIdentity] [] graph
    steveAssurancePolicy (Map.elems (ledgerEvidence ledger))
  let systems = stageSystemsArtifact stage
      context = emptyVerificationContext
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationPhilCoreDigest = digestText
            (canonicalSemanticForm (coreSystemsProgramSemanticForm steveCoreProgram))
        , verificationImplementationDigest = systemsArtifactDigest systems
        , verificationTarget = "phase1-steve"
        , verificationCompilationProfile = "phase1/int002/certified-release"
        , verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        , verificationPermittedAssumptions = assumptionIds
        , verificationPermittedExportBoundaries = Set.empty
        , verificationAvailableArtifacts = Map.empty
        , verificationLoweringLedgerRoot = loweringLedgerRoot
            (systemsArtifactLoweringLedger systems)
        , verificationKnownCostRefs = Set.empty
        , verificationValidityContext = validity
        }
      selection = ManifestClosureSelection
        { manifestClosureEvidence = evidenceIds
        , manifestClosureAssumptions = assumptionIds
        , manifestClosureExports = Map.empty
        , manifestClosureUses = Set.empty
        }
  manifest <- mapLeft show $ closeVerificationBundle bundle steveAssurancePolicy
    context ledger selection
  Right RealManifestFixture
    { realFixtureContext = context
    , realFixtureLedger = ledger
    , realFixtureManifest = manifest
    , realFixtureStage = stage
    }

stageSystemsArtifact :: StageClosureBundle -> SystemsArtifact
stageSystemsArtifact = phase1StageSystemsArtifact
  . subjectStageBase
  . concreteSubjectStage
  . stageClosureConcrete

uploadAssurancePolicy :: ApplicationAssurancePolicy
uploadAssurancePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision =
      AssurancePolicyRevision "phase1.int002.upload.certified-release.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.fromList
      [ StaticallyDischarged, RuntimeBound, ExternallyDischarged
      , AssumptionDependent, Exported, DeploymentExported
      ]
  }

checkedUploadArchitecture :: Text -> Text -> Either String CheckedSourceArchitecture
checkedUploadArchitecture clientSource serverSource = do
  clientEnvironment <- mapLeft show (phase0EnvironmentFor "client.phil")
  serverEnvironment <- mapLeft show (phase0EnvironmentFor "server.phil")
  checked <- mapLeft show $ checkPortableSourceBundle uploadRoots
    (Map.fromList
      [ (uploadClientDeclaration, clientEnvironment)
      , (uploadServerDeclaration, serverEnvironment)
      ])
    (PortableSourceBundle canonicalGrammarRevisionV1 "program:upload"
      [ PortableSourceUnit (SourceUnitId "unit.upload.client")
          (DeclarationSiteId "site.upload.client") (Just "decl:upload.client") clientSource
      , PortableSourceUnit (SourceUnitId "unit.upload.server")
          (DeclarationSiteId "site.upload.server") (Just "decl:upload.server") serverSource
      ]
      [PortableInstanceLineage (InstanceLineageSiteId "instance.upload") "inst:phase1.upload"]
      [])
  mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:upload" (InstanceLineageSiteId "instance.upload")) checked

uploadRoots :: SourceRootMap
uploadRoots = Map.singleton "program:upload" uploadServerDeclaration

uploadClientDeclaration, uploadServerDeclaration :: DeclarationKey
uploadClientDeclaration = DeclarationKey "decl:upload.client"
uploadServerDeclaration = DeclarationKey "decl:upload.server"

steveAssurancePolicy :: ApplicationAssurancePolicy
steveAssurancePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision =
      AssurancePolicyRevision "phase1.int002.steve.certified-release.v1"
  , applicationAssurancePolicyPermittedDispositions =
      Set.fromList [StaticallyDischarged, AssumptionDependent]
  }

checkedSteveArchitecture :: Text -> Text -> Either String CheckedSourceArchitecture
checkedSteveArchitecture putSource getSource = do
  checked <- mapLeft show $ checkPortableSourceBundle steveRoots steveEnvironments
    (PortableSourceBundle canonicalGrammarRevisionV1 "program:steve"
      [ PortableSourceUnit (SourceUnitId "unit.steve.put")
          (DeclarationSiteId "site.steve.put") (Just "decl:steve.put") putSource
      , PortableSourceUnit (SourceUnitId "unit.steve.get")
          (DeclarationSiteId "site.steve.get") (Just "decl:steve.get") getSource
      ]
      [PortableInstanceLineage (InstanceLineageSiteId "instance.steve") "inst:phase1.steve"]
      [])
  mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:steve" (InstanceLineageSiteId "instance.steve")) checked

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
digestComputePrimitive = PrimitiveProviderDecision [PrimitiveReadOnly]
  [ProviderOutcomeSpec "computed" [(Unrestricted, contentIdType)]]

blobInstallPrimitive :: PrimitiveSemantics
blobInstallPrimitive = PrimitiveProviderDecision [PrimitiveReadOnly, PrimitiveConsume]
  [ ProviderOutcomeSpec "installed" []
  , ProviderOutcomeSpec "already-exists" []
  , ProviderOutcomeSpec "storage-failure" [(Unrestricted, storageFailureType)]
  ]

blobReadPrimitive :: PrimitiveSemantics
blobReadPrimitive = PrimitiveProviderDecision [PrimitiveReadOnly]
  [ ProviderOutcomeSpec "found" [(Linear, ownedBytesType)]
  , ProviderOutcomeSpec "not-found" []
  , ProviderOutcomeSpec "storage-failure" [(Unrestricted, storageFailureType)]
  ]

digestCheckPrimitive :: PrimitiveSemantics
digestCheckPrimitive = PrimitiveProviderDecision [PrimitiveReadOnly, PrimitiveReadOnly]
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

data ProviderLedgerEntries = ProviderLedgerEntries
  { providerLedgerRevisions :: Map.Map RevisionId ObligationRevision
  , providerLedgerEvidence :: Map.Map EvidenceEntryId EvidenceEntry
  , providerLedgerAssumptions :: Map.Map AssumptionId Assumption
  }

providerLedgerEntries :: Map.Map Text Text -> SteveProviderQualificationArtifact -> ProviderLedgerEntries
providerLedgerEntries validity artifact = ProviderLedgerEntries
  { providerLedgerRevisions = Map.fromList
      [ (revisionId revision, revision)
      | (key, disposition) <- Map.toAscList dispositions
      , let revision = providerObligationRevision artifact key disposition
      ]
  , providerLedgerEvidence = Map.fromList
      [ (evidenceEntryId entry, entry)
      | (key, disposition) <- Map.toAscList dispositions
      , let revision = providerObligationRevision artifact key disposition
            entry = providerEvidenceEntry validity artifact key disposition revision
      ]
  , providerLedgerAssumptions = Map.fromList
      [ (assumptionId assumption, assumption)
      | condition <- Set.toAscList (providerAssumptionRefs artifact)
      , let assumption = providerAssumption validity artifact condition
      ]
  }
  where
    dispositions = qualificationEvidenceObligationDispositions
      (steveProviderIdentityEvidence artifact)

mergeProviderLedgerEntries :: ProviderLedgerEntries -> ProviderLedgerEntries
  -> Either String (AssuranceLedger, Set.Set EvidenceEntryId, Set.Set AssumptionId)
mergeProviderLedgerEntries left right = do
  revisions <- disjointUnion "revision" providerLedgerRevisions
  evidence <- disjointUnion "evidence" providerLedgerEvidence
  assumptions <- disjointUnion "assumption" providerLedgerAssumptions
  let ledger = emptyLedger
        { ledgerRevisions = revisions
        , ledgerEvidence = evidence
        , ledgerAssumptions = assumptions
        }
  Right (ledger, Map.keysSet evidence, Map.keysSet assumptions)
  where
    disjointUnion :: (Ord key, Show key) => String
      -> (ProviderLedgerEntries -> Map.Map key value)
      -> Either String (Map.Map key value)
    disjointUnion label project =
      let leftMap = project left
          rightMap = project right
          overlap = Map.keysSet leftMap `Set.intersection` Map.keysSet rightMap
      in case Set.lookupMin overlap of
          Nothing -> Right (Map.union leftMap rightMap)
          Just key -> Left ("cross-provider " <> label <> " identity collision: " <> show key)

providerObligationRevision :: SteveProviderQualificationArtifact -> Text -> SemanticForm -> ObligationRevision
providerObligationRevision artifact key disposition = revision
  where
    kind = KernelChecked
    role = providerEvidenceRole artifact
    statement = Text.intercalate " | "
      ["Steve provider qualification obligation", steveProviderLabel artifact, key, canonicalSemanticForm disposition]
    provisional = ObligationRevision
      { revisionObligationId = ObligationId (providerOccurrence artifact <> "." <> key)
      , revisionId = RevisionId ""
      , revisionStatement = statement
      , revisionStatementDigest = digestText statement
      , revisionKind = "provider-qualification"
      , revisionOrigin = "Phil.Examples.Steve.ProviderQualifications"
      , revisionScope = "Steve provider qualification"
      , revisionRequiredAt = "application manifest closure"
      , revisionRepresentation = "ProviderQualificationEvidenceIdentityInput"
      , revisionSubjectIds = [providerOccurrence artifact]
      , revisionContextIds =
          [ unQualificationClaimRevision (qualificationEvidenceClaimRevision (steveProviderIdentityEvidence artifact))
          , unQualificationEvidenceRevision (deriveQualificationEvidenceRevision (steveProviderIdentityEvidence artifact))
          ]
      , revisionAcceptanceRule = AcceptEntry kind role
      , revisionGeneratedFrom = []
      }
    revision = provisional { revisionId = deriveRevisionId provisional }

providerEvidenceEntry :: Map.Map Text Text -> SteveProviderQualificationArtifact -> Text
  -> SemanticForm -> ObligationRevision -> EvidenceEntry
providerEvidenceEntry validity artifact key disposition revision = entry
  where
    kind = KernelChecked
    assumptions = map AssumptionId (Set.toAscList (providerAssumptionRefs artifact))
    admission = steveProviderCheckedAdmission artifact
    provisional = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId (Text.intercalate ":" ["evidence", providerOccurrence artifact, key])
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = kind
      , evidenceRole = providerEvidenceRole artifact
      , evidenceProducer = "Steve provider qualification pipeline"
      , evidenceChecker = "SteveProviderQualificationWitnessKernel"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = map digestText
          [ unQualificationClaimRevision (checkedQualificationAdmissionClaimRevision admission)
          , unQualificationEvidenceRevision (checkedQualificationAdmissionEvidenceRevision admission)
          , unQualificationAdmissionRevision (checkedQualificationAdmissionRevision admission)
          ]
      , evidenceAssumptions = assumptions
      , evidenceDependsOn = []
      , evidenceValidityScope = ValidityScope validity
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = [key, canonicalSemanticForm disposition]
          <> Set.toAscList (qualificationEvidenceRefs (steveProviderIdentityEvidence artifact))
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }
    entry = provisional { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }

providerAssumption :: Map.Map Text Text -> SteveProviderQualificationArtifact -> Text -> Assumption
providerAssumption validity artifact condition = assumption
  where
    provisional = Assumption
      { assumptionId = AssumptionId condition
      , assumptionDigest = Digest ""
      , assumptionStatement = condition
      , assumptionScope = "Steve provider qualification condition"
      , assumptionOwnerBoundary = providerOccurrence artifact
      , assumptionRationale = "Explicit condition carried by the admitted Steve provider qualification"
      , assumptionValidityScope = ValidityScope validity
      }
    assumption = provisional { assumptionDigest = deriveAssumptionDigest provisional }

providerAssumptionRefs :: SteveProviderQualificationArtifact -> Set.Set Text
providerAssumptionRefs = qualificationEvidenceAssumptionRefs . steveProviderIdentityEvidence

providerEvidenceRole :: SteveProviderQualificationArtifact -> EvidenceRole
providerEvidenceRole artifact = EvidenceRole
  ("steve.provider-qualification:" <> providerOccurrence artifact)

providerOccurrence :: SteveProviderQualificationArtifact -> Text
providerOccurrence = checkedQualificationAdmissionProviderOccurrence . steveProviderCheckedAdmission

steveValidityContext :: SteveProviderQualificationArtifact -> SteveProviderQualificationArtifact
  -> Map.Map Text Text
steveValidityContext digestArtifact blobArtifact = Map.fromList
  ([ ("witness", "Steve") ] <> providerValidity "digest" digestArtifact <> providerValidity "blob" blobArtifact)
  where
    providerValidity prefix artifact =
      let admission = steveProviderCheckedAdmission artifact
      in [ (prefix <> ".claim", unQualificationClaimRevision (checkedQualificationAdmissionClaimRevision admission))
         , (prefix <> ".evidence", unQualificationEvidenceRevision (checkedQualificationAdmissionEvidenceRevision admission))
         , (prefix <> ".admission", unQualificationAdmissionRevision (checkedQualificationAdmissionRevision admission))
         ]

sourceDeclarationIdentity :: CheckedSourceUnit -> DeclarationIdentity
sourceDeclarationIdentity unit = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "ordinary-source" []
  , declarationKey = checkedSourceDeclarationKey unit
  , declarationInterfaceSemantics = sourceComponentInterfaceSemantics component
  , declarationDefinitionSemantics = sourceComponentDefinitionSemantics component
  }
  where
    component = locatedValue (checkedSourceComponent unit)

deriveSourceRevision :: Text -> [DeclarationIdentity] -> ArchitectureInstanceIdentity -> Digest
deriveSourceRevision prefix declarations instanceIdentity = digestText (Text.intercalate "\n"
  (prefix : map renderDeclaration ordered <> ["instance=" <> renderInstance instanceIdentity]))
  where
    ordered = Set.toAscList (Set.fromList declarations)
    renderDeclaration identity = Text.intercalate "@"
      [ unDeclarationKey (identityDeclarationKey identity)
      , unInterfaceRevision (identityInterfaceRevision identity)
      , unDefinitionRevision (identityDefinitionRevision identity)
      ]
    renderInstance identity = Text.intercalate "@"
      [ unInstanceKey (identityInstanceKey identity)
      , unInstanceRevision (identityInstanceRevision identity)
      ]

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
