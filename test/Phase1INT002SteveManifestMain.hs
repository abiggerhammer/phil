{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Phase0 (phase0UploadLedger)
import Phil.Assurance.Types
import Phil.Assurance.Verify (verifyManifest)
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
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveCoreProgram
  , stevePhase1StageBundle
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
import Phil.Surface.Syntax (Located (..))
import Phil.Systems.GenericLowering (coreSystemsProgramSemanticForm)
import Phil.Systems.IR
  ( loweringLedgerRoot
  , systemsArtifactDigest
  , systemsArtifactLoweringLedger
  )
import Phil.Systems.Phase1Stage
  ( phase1StageSystemsArtifact
  , verifyPhase1StageBundle
  )
import Phil.Verification
import Phil.Verification.Bundle
import Phil.Verification.ManifestClosure
import System.Exit (exitFailure)

main :: IO ()
main = do
  putSource <- TextIO.readFile "examples/steve/put.phil"
  getSource <- TextIO.readFile "examples/steve/get.phil"
  results <- sequence
    [ test "INT-002 ordinary Steve source closes a real manifest through the generic path"
        (steveManifestCloses putSource getSource)
    , test "INT-002 Steve manifest rejects Upload evidence inheritance"
        (uploadEvidenceInheritanceRejected putSource getSource)
    , test "INT-002 Steve qualification assumptions remain explicit and validity-scoped"
        (steveAssumptionsExplicit putSource getSource)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

steveManifestCloses :: Text -> Text -> Either String ()
steveManifestCloses putSource getSource = do
  (bundle, context, ledger, selection) <- steveClosureFixture putSource getSource
  manifest <- mapLeft show $ closeVerificationBundle
    bundle steveAssurancePolicy context ledger selection
  mapLeft show (verifyManifest context ledger manifest)
  assert
    (manifestArchitectureDigest manifest == verificationBundleArchitectureDigest bundle)
    "accepted Steve manifest is not bound to the ordinary-source Architecture identity"
  assert
    (manifestObligationRevisions manifest == Map.keysSet
      (verificationGraphNodes (verificationBundleObligationGraph bundle)))
    "accepted Steve manifest changed the VerificationBundle obligation domain"
  assert
    (manifestEvidenceEntries manifest == manifestClosureEvidence selection)
    "accepted Steve manifest changed the explicit evidence selection"
  assert
    (manifestAssumptionNodes manifest == manifestClosureAssumptions selection)
    "accepted Steve manifest hid or invented assumptions"
  assert
    (Set.null (manifestExports manifest))
    "Steve unexpectedly exported an in-scope provider obligation"

uploadEvidenceInheritanceRejected :: Text -> Text -> Either String ()
uploadEvidenceInheritanceRejected putSource getSource = do
  (bundle, context, ledger, selection) <- steveClosureFixture putSource getSource
  foreignEvidence <- case Map.keys (ledgerEvidence phase0UploadLedger) of
    [] -> Left "Upload assurance ledger unexpectedly has no evidence entries"
    entry : _ -> Right entry
  assert
    (not (Map.member foreignEvidence (ledgerEvidence ledger)))
    "Steve ledger unexpectedly contains the selected Upload evidence entry"
  let contaminated = selection
        { manifestClosureEvidence = Set.insert foreignEvidence
            (manifestClosureEvidence selection) }
  case closeVerificationBundle bundle steveAssurancePolicy context ledger contaminated of
    Left (ManifestClosureSelectedEvidenceMissing entry)
      | entry == foreignEvidence -> Right ()
    other -> Left ("expected foreign Upload evidence rejection, got " <> show other)

steveAssumptionsExplicit :: Text -> Text -> Either String ()
steveAssumptionsExplicit putSource getSource = do
  (bundle, context, ledger, selection) <- steveClosureFixture putSource getSource
  qualifications <- mapLeft (show . unSteveProviderQualificationError)
    materializeSteveProviderQualifications
  let expected = Set.map AssumptionId $ Set.unions
        [ providerAssumptionRefs (steveDigestProviderQualification qualifications)
        , providerAssumptionRefs (steveBlobProviderQualification qualifications)
        ]
  assert
    (manifestClosureAssumptions selection == expected)
    "Steve closure selection does not expose the exact provider qualification assumptions"
  mapM_ (checkAssumptionScope context ledger) (Set.toAscList expected)
  manifest <- mapLeft show $ closeVerificationBundle
    bundle steveAssurancePolicy context ledger selection
  assert
    (manifestAssumptionNodes manifest == expected)
    "accepted Steve manifest did not retain the exact explicit assumption set"

checkAssumptionScope
  :: VerificationContext
  -> AssuranceLedger
  -> AssumptionId
  -> Either String ()
checkAssumptionScope context ledger key = case Map.lookup key (ledgerAssumptions ledger) of
  Nothing -> Left ("missing Steve assumption " <> show key)
  Just assumption ->
    let ValidityScope dimensions = assumptionValidityScope assumption
    in assert
      (not (Map.null dimensions)
        && all (\(name, value) -> Map.lookup name
              (verificationValidityContext context) == Just value)
            (Map.toList dimensions))
      ("Steve assumption lacks an exact validity scope: " <> show key)

steveClosureFixture
  :: Text
  -> Text
  -> Either String
      (VerificationBundle, VerificationContext, AssuranceLedger, ManifestClosureSelection)
steveClosureFixture putSource getSource = do
  architecture <- checkedSteveArchitecture putSource getSource
  qualifications <- mapLeft (show . unSteveProviderQualificationError)
    materializeSteveProviderQualifications
  stageBundle <- stevePhase1StageBundle
  mapLeft show (verifyPhase1StageBundle stageBundle)
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
      architectureIdentity =
        checkedArchitectureIdentity (checkedSourceArchitectureRoot architecture)
      sourceRevision = deriveSourceRevision declarations architectureIdentity
  bundle <- mapLeft show $ buildVerificationBundle
    sourceRevision
    declarations
    [architectureIdentity]
    []
    graph
    steveAssurancePolicy
    (Map.elems (ledgerEvidence ledger))
  let stageArtifact = phase1StageSystemsArtifact stageBundle
      context = emptyVerificationContext
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationPhilCoreDigest = digestText
            (canonicalSemanticForm (coreSystemsProgramSemanticForm steveCoreProgram))
        , verificationImplementationDigest = systemsArtifactDigest stageArtifact
        , verificationTarget = "phase1-steve"
        , verificationCompilationProfile = "phase1/int002/certified-release"
        , verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        , verificationPermittedAssumptions = assumptionIds
        , verificationPermittedExportBoundaries = Set.empty
        , verificationAvailableArtifacts = Map.empty
        , verificationLoweringLedgerRoot =
            loweringLedgerRoot (systemsArtifactLoweringLedger stageArtifact)
        , verificationKnownCostRefs = Set.empty
        , verificationValidityContext = validity
        }
      selection = ManifestClosureSelection
        { manifestClosureEvidence = evidenceIds
        , manifestClosureAssumptions = assumptionIds
        , manifestClosureExports = Map.empty
        , manifestClosureUses = Set.empty
        }
  Right (bundle, context, ledger, selection)

-- | Assurance data is derived from each admitted provider qualification artifact.
-- The generic closure path never receives a witness name or branch discriminator.
data ProviderLedgerEntries = ProviderLedgerEntries
  { providerLedgerRevisions :: Map.Map RevisionId ObligationRevision
  , providerLedgerEvidence :: Map.Map EvidenceEntryId EvidenceEntry
  , providerLedgerAssumptions :: Map.Map AssumptionId Assumption
  }

providerLedgerEntries
  :: Map.Map Text Text
  -> SteveProviderQualificationArtifact
  -> ProviderLedgerEntries
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

mergeProviderLedgerEntries
  :: ProviderLedgerEntries
  -> ProviderLedgerEntries
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
    disjointUnion
      :: (Ord key, Show key)
      => String
      -> (ProviderLedgerEntries -> Map.Map key value)
      -> Either String (Map.Map key value)
    disjointUnion label project =
      let leftMap = project left
          rightMap = project right
          overlap = Map.keysSet leftMap `Set.intersection` Map.keysSet rightMap
      in case Set.lookupMin overlap of
          Nothing -> Right (Map.union leftMap rightMap)
          Just key -> Left ("cross-provider " <> label <> " identity collision: " <> show key)

providerObligationRevision
  :: SteveProviderQualificationArtifact
  -> Text
  -> SemanticForm
  -> ObligationRevision
providerObligationRevision artifact key disposition = revision
  where
    kind = KernelChecked
    role = providerEvidenceRole artifact
    statement = Text.intercalate " | "
      [ "Steve provider qualification obligation"
      , steveProviderLabel artifact
      , key
      , canonicalSemanticForm disposition
      ]
    provisional = ObligationRevision
      { revisionObligationId = ObligationId
          (providerOccurrence artifact <> "." <> key)
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
          [ unQualificationClaimRevision
              (qualificationEvidenceClaimRevision
                (steveProviderIdentityEvidence artifact))
          , unQualificationEvidenceRevision
              (deriveQualificationEvidenceRevision
                (steveProviderIdentityEvidence artifact))
          ]
      , revisionAcceptanceRule = AcceptEntry kind role
      , revisionGeneratedFrom = []
      }
    revision = provisional { revisionId = deriveRevisionId provisional }

providerEvidenceEntry
  :: Map.Map Text Text
  -> SteveProviderQualificationArtifact
  -> Text
  -> SemanticForm
  -> ObligationRevision
  -> EvidenceEntry
providerEvidenceEntry validity artifact key disposition revision = entry
  where
    kind = KernelChecked
    assumptions = map AssumptionId
      (Set.toAscList (providerAssumptionRefs artifact))
    evidenceId = EvidenceEntryId (Text.intercalate ":"
      [ "evidence"
      , providerOccurrence artifact
      , key
      ])
    admission = steveProviderCheckedAdmission artifact
    identityEvidence = steveProviderIdentityEvidence artifact
    provisional = EvidenceEntry
      { evidenceEntryId = evidenceId
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = kind
      , evidenceRole = providerEvidenceRole artifact
      , evidenceProducer = "Steve provider qualification pipeline"
      , evidenceChecker = "SteveProviderQualificationWitnessKernel"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = map digestText
          [ unQualificationClaimRevision
              (checkedQualificationAdmissionClaimRevision admission)
          , unQualificationEvidenceRevision
              (checkedQualificationAdmissionEvidenceRevision admission)
          , unQualificationAdmissionRevision
              (checkedQualificationAdmissionRevision admission)
          ]
      , evidenceAssumptions = assumptions
      , evidenceDependsOn = []
      , evidenceValidityScope = ValidityScope validity
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies =
          [ key
          , canonicalSemanticForm disposition
          ] <> Set.toAscList (qualificationEvidenceRefs identityEvidence)
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }
    entry = provisional { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }

providerAssumption
  :: Map.Map Text Text
  -> SteveProviderQualificationArtifact
  -> Text
  -> Assumption
providerAssumption validity artifact condition = assumption
  where
    key = AssumptionId condition
    provisional = Assumption
      { assumptionId = key
      , assumptionDigest = Digest ""
      , assumptionStatement = condition
      , assumptionScope = "Steve provider qualification condition"
      , assumptionOwnerBoundary = providerOccurrence artifact
      , assumptionRationale =
          "Explicit condition carried by the admitted Steve provider qualification"
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

steveValidityContext
  :: SteveProviderQualificationArtifact
  -> SteveProviderQualificationArtifact
  -> Map.Map Text Text
steveValidityContext digestArtifact blobArtifact = Map.fromList
  ([ ("witness", "Steve") ]
    <> providerValidity "digest" digestArtifact
    <> providerValidity "blob" blobArtifact)
  where
    providerValidity prefix artifact =
      let admission = steveProviderCheckedAdmission artifact
      in [ (prefix <> ".claim",
              unQualificationClaimRevision
                (checkedQualificationAdmissionClaimRevision admission))
         , (prefix <> ".evidence",
              unQualificationEvidenceRevision
                (checkedQualificationAdmissionEvidenceRevision admission))
         , (prefix <> ".admission",
              unQualificationAdmissionRevision
                (checkedQualificationAdmissionRevision admission))
         ]

steveAssurancePolicy :: ApplicationAssurancePolicy
steveAssurancePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision =
      AssurancePolicyRevision "phase1.int002.steve.certified-release.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.fromList
      [ StaticallyDischarged
      , AssumptionDependent
      ]
  }

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

sourceDeclarationIdentity :: CheckedSourceUnit -> DeclarationIdentity
sourceDeclarationIdentity unit = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "ordinary-source" []
  , declarationKey = checkedSourceDeclarationKey unit
  , declarationInterfaceSemantics = sourceComponentInterfaceSemantics component
  , declarationDefinitionSemantics = sourceComponentDefinitionSemantics component
  }
  where
    component = locatedValue (checkedSourceComponent unit)

deriveSourceRevision
  :: [DeclarationIdentity]
  -> ArchitectureInstanceIdentity
  -> Digest
deriveSourceRevision declarations instanceIdentity = digestText (Text.intercalate "\n"
  ("phase1-int002-steve-source-v1" : map renderDeclaration ordered
    <> ["instance=" <> renderInstance instanceIdentity]))
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

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
