{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.SourceSystems
  ( SourceSystemsAdmission
  , SourceSystemsError (..)
  , prepareSourceSystemsAdmission
  , lowerSourceSystems
  , VerifiedSourceSystemsProduction
  , VerifiedSourceCheckEventGraph
  , verifiedSourceSystemsCheckEventGraph
  , verifiedSourceCheckEventOccurrences
  , verifiedSourceCheckEventArchitectureIdentity
  , verifiedSourceCheckEventCoreSemantics
  , VerifiedSourceSystemsProductionError (..)
  , produceVerifiedSourceSystems
  , verifiedSourceSystemsArchitectureIdentity
  , verifiedSourceSystemsArchitectureDescriptor
  , verifiedSourceSystemsStage
  , sourceSystemsArchitectureIdentity
  , sourceSystemsProgramSemantics
  , VerifiedSteveGetStructural
  , VerifiedSteveGetStructuralError (..)
  , verifyOriginalSteveGetStructural
  , VerifiedSteveGetCanonicalSource
  , VerifiedSteveGetCanonicalError (..)
  , produceVerifiedSteveGetCanonicalSource
  , verifiedSteveGetCanonicalSourceProduction
  , verifiedSteveGetCanonicalSelectedAssumptions
  , VerifiedSteveGetModeledABI
  , VerifiedSteveGetModeledABIError (..)
  , verifyOriginalSteveGetModeledABI
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Syntax (Mode (..), Ty (..))
import Phil.Examples.Steve.ApplicationShell (steveGetShellEnvironment)
import Phil.Examples.Steve.ProviderQualifications
  ( SteveProviderQualifications (..)
  , SteveProviderQualificationArtifact (..)
  , SteveProviderQualificationError
  , materializeSteveProviderQualifications
  )
import Phil.Core.ProviderQualificationIdentity
  ( ProviderQualificationClaimIdentityInput (..))
import Phil.Surface.Check.Types
  ( InitialBinding (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , emptySurfaceEnvironment
  )
import Phil.Compiler.SourceArchitecture
  ( CheckedSourceArchitecture (..)
  , SourceArchitectureError
  , SourceArchitectureRootMap
  , buildCheckedSourceArchitecture
  )
import Phil.Compiler.SourceBundle
  ( CheckedSourceEvidenceOccurrence
  , checkedSourceEvidenceOccurrences
  , SourceBundleCheckError
  , SourceEnvironmentMap
  , SourceRootMap
  , checkPortableSourceBundle
  )
import Phil.Compiler.SourceCore
  ( CheckedSourceCoreCorrespondence
  , SourceCoreCorrespondenceError
  , sourceCoreArchitectureIdentity
  , sourceCoreProgramSemantics
  , verifySourceCoreCorrespondence
  )
import Phil.Compiler.SourceCorePolicy
  ( SourceCoreCorrespondencePolicy
  , SourceCorePolicyError
  , SteveGetStructuralError
  , SteveGetStructuralFact
  , verifySourceCorePolicy
  , verifySteveGetStructural
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  , ArchitectureInstanceDescriptor
  , ArchitectureInstanceIdentity
  , SemanticForm
  , checkedArchitectureDescriptor
  , checkedArchitectureIdentity
  , identityInstanceRevision
  )
import Phil.Compiler.RuntimeChoicePayload
  ( RuntimeChoicePayloadPlan, RuntimeChoiceSite (..) )
import Phil.Compiler.RuntimeChoiceSystems
  ( RuntimeChoiceSystemsError, bindRuntimeChoicePayloadPlan )
import Phil.Compiler.RuntimeChoiceABI
  ( RuntimeChoiceABIError, RuntimeChoiceABICarrier (..)
  , RuntimeChoiceABIInput (..), RuntimeChoiceABIArm (..)
  , RuntimeChoiceABIPlan, RuntimeChoiceABISite (..)
  , certifyRuntimeChoiceABIPlan, runtimeChoiceABISites )
import Phil.Compiler.RuntimeChoiceLLVM
  ( RuntimeChoiceLLVMError, RuntimeChoiceLLVMArtifact (..)
  , phase1RuntimeChoiceLLVMTarget, lowerRuntimeChoiceABIToLLVM )
import Phil.Systems.IR (ValueId (..), BlockId (..))
import Phil.Systems.GenericLowering
  ( CoreSystemsProgram
  , GenericLoweringError
  , GenericRealizationContext
  , coreSystemsProgramSemanticForm
  , lowerGenericSystems
  )
import Phil.Systems.Phase1Stage (Phase1StageBundle (..))
import Phil.Surface.Lineage (PortableSourceBundle)

-- | Opaque admission object sealing the exact source-derived Architecture and
-- CoreSystemsProgram pair that passed both structural correspondence and the
-- complete independent source-call/branch correspondence policy. Callers cannot
-- replace either member between verification and lowering.
data SourceSystemsAdmission = SourceSystemsAdmission
  CheckedSourceArchitecture
  CoreSystemsProgram
  CheckedSourceCoreCorrespondence
  deriving (Eq, Show)

data SourceSystemsError
  = SourceSystemsCorrespondenceRejected SourceCoreCorrespondenceError
  | SourceSystemsPolicyRejected SourceCorePolicyError
  | SourceSystemsAdmissionArchitectureDrift
  | SourceSystemsAdmissionProgramDrift
  | SourceSystemsLoweringRejected GenericLoweringError
  deriving (Eq, Show)

prepareSourceSystemsAdmission
  :: SourceCoreCorrespondencePolicy
  -> CheckedSourceArchitecture
  -> CoreSystemsProgram
  -> Either SourceSystemsError SourceSystemsAdmission
prepareSourceSystemsAdmission policy architecture program = do
  correspondence <- mapLeft SourceSystemsCorrespondenceRejected
    (verifySourceCoreCorrespondence architecture program)
  mapLeft SourceSystemsPolicyRejected
    (verifySourceCorePolicy policy architecture program)
  Right (SourceSystemsAdmission architecture program correspondence)

lowerSourceSystems
  :: SourceSystemsAdmission
  -> GenericRealizationContext
  -> Either SourceSystemsError Phase1StageBundle
lowerSourceSystems (SourceSystemsAdmission architecture program correspondence) context = do
  if checkedArchitectureIdentity (checkedSourceArchitectureRoot architecture)
      == sourceCoreArchitectureIdentity correspondence
    then Right ()
    else Left SourceSystemsAdmissionArchitectureDrift
  if coreSystemsProgramSemanticForm program == sourceCoreProgramSemantics correspondence
    then Right ()
    else Left SourceSystemsAdmissionProgramDrift
  mapLeft SourceSystemsLoweringRejected
    (lowerGenericSystems
      (checkedSourceArchitectureRoot architecture)
      program
      context)

-- | The exact stage produced by an ordinary checked-source/checked-Core
-- event, paired with that event's complete sealed admission (including K/I).
-- Its constructor is private; caller-created CheckedSourceArchitecture values
-- cannot enter the stronger producing function below.
-- This is NOT a StageClosure or CertifiedRelease origin certificate.
-- | Private provenance of original *static checker* observations from the
-- rechecked raw source bundle and the exact already-admitted Core/Architecture
-- pair. The constructor is private: public CheckedSourceUnit/Surface results
-- and copied evidence arrays cannot construct this witness. This witnesses
-- P2 transport, NOT an actual later P7 assurance use, universal Core op-event
-- simulation, SYS-012 completeness or SYS-013 discharge.
data VerifiedSourceCheckEventGraph = VerifiedSourceCheckEventGraph
  [CheckedSourceEvidenceOccurrence]
  ArchitectureInstanceIdentity
  SemanticForm
  deriving (Eq, Show)

data VerifiedSourceSystemsProduction = VerifiedSourceSystemsProduction
  SourceSystemsAdmission
  Phase1StageBundle
  VerifiedSourceCheckEventGraph
  deriving (Eq, Show)

verifiedSourceCheckEventOccurrences
  :: VerifiedSourceCheckEventGraph -> [CheckedSourceEvidenceOccurrence]
verifiedSourceCheckEventOccurrences (VerifiedSourceCheckEventGraph events _ _) = events

verifiedSourceCheckEventArchitectureIdentity
  :: VerifiedSourceCheckEventGraph -> ArchitectureInstanceIdentity
verifiedSourceCheckEventArchitectureIdentity
  (VerifiedSourceCheckEventGraph _ identity _) = identity

verifiedSourceCheckEventCoreSemantics
  :: VerifiedSourceCheckEventGraph -> SemanticForm
verifiedSourceCheckEventCoreSemantics
  (VerifiedSourceCheckEventGraph _ _ semantics) = semantics

verifiedSourceSystemsCheckEventGraph
  :: VerifiedSourceSystemsProduction -> VerifiedSourceCheckEventGraph
verifiedSourceSystemsCheckEventGraph
  (VerifiedSourceSystemsProduction _ _ graph) = graph

data VerifiedSourceSystemsProductionError
  = VerifiedSourceBundleRejected SourceBundleCheckError
  | VerifiedSourceArchitectureRejected SourceArchitectureError
  | VerifiedSourceAdmissionRejected SourceSystemsError
  | VerifiedSourceLoweringRejected SourceSystemsError
  | VerifiedSourceInstanceRevisionDrift
  deriving (Eq, Show)

-- | Recheck raw ordinary source/lineage rather than accepting a public
-- "checked" record. Preserve its exact K and I next to the complete stage
-- from the actual admitted generic Core-to-Systems lowering event.
-- Source environments and Core correspondence policy remain the existing
-- Phase 1 authority inputs, not newly proved compiler facts.
produceVerifiedSourceSystems
  :: SourceRootMap
  -> SourceEnvironmentMap
  -> SourceArchitectureRootMap
  -> SourceCoreCorrespondencePolicy
  -> PortableSourceBundle
  -> CoreSystemsProgram
  -> GenericRealizationContext
  -> Either VerifiedSourceSystemsProductionError VerifiedSourceSystemsProduction
produceVerifiedSourceSystems roots environments sites policy portable program context = do
  checked <- mapLeft VerifiedSourceBundleRejected
    (checkPortableSourceBundle roots environments portable)
  architecture <- mapLeft VerifiedSourceArchitectureRejected
    (buildCheckedSourceArchitecture sites checked)
  admitted <- mapLeft VerifiedSourceAdmissionRejected
    (prepareSourceSystemsAdmission policy architecture program)
  stage <- mapLeft VerifiedSourceLoweringRejected
    (lowerSourceSystems admitted context)
  let graph = VerifiedSourceCheckEventGraph
        (checkedSourceEvidenceOccurrences checked)
        (sourceSystemsArchitectureIdentity admitted)
        (sourceSystemsProgramSemantics admitted)
  if phase1StageInstanceRevision stage ==
      identityInstanceRevision (sourceSystemsArchitectureIdentity admitted)
    then Right (VerifiedSourceSystemsProduction admitted stage graph)
    else Left VerifiedSourceInstanceRevisionDrift

verifiedSourceSystemsArchitectureIdentity
  :: VerifiedSourceSystemsProduction -> ArchitectureInstanceIdentity
verifiedSourceSystemsArchitectureIdentity
  (VerifiedSourceSystemsProduction admitted _ _) =
    sourceSystemsArchitectureIdentity admitted

-- | The exact descriptor independently rederived from the raw ordinary source
-- and sealed in the checked producer. Full K, parent, declaration, and
-- semantic actuals survive; no caller-created checked record is accepted.
verifiedSourceSystemsArchitectureDescriptor
  :: VerifiedSourceSystemsProduction -> ArchitectureInstanceDescriptor
verifiedSourceSystemsArchitectureDescriptor
  (VerifiedSourceSystemsProduction (SourceSystemsAdmission architecture _ _) _ _) =
    checkedArchitectureDescriptor (checkedSourceArchitectureRoot architecture)

verifiedSourceSystemsStage
  :: VerifiedSourceSystemsProduction -> Phase1StageBundle
verifiedSourceSystemsStage (VerifiedSourceSystemsProduction _ stage _) = stage

sourceSystemsArchitectureIdentity
  :: SourceSystemsAdmission
  -> ArchitectureInstanceIdentity
sourceSystemsArchitectureIdentity
  (SourceSystemsAdmission _ _ correspondence) =
    sourceCoreArchitectureIdentity correspondence

sourceSystemsProgramSemantics
  :: SourceSystemsAdmission
  -> SemanticForm
sourceSystemsProgramSemantics
  (SourceSystemsAdmission _ _ correspondence) =
    sourceCoreProgramSemantics correspondence

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right


-- | A private, raw-source-rechecked STEVEGET STRUCTURAL discriminator only.
-- This is not a native owner/loan/ABI or P9 final-use certificate.
data VerifiedSteveGetStructural = VerifiedSteveGetStructural
  VerifiedSourceSystemsProduction
  SteveGetStructuralFact
  deriving (Eq, Show)

data VerifiedSteveGetStructuralError
  = VerifiedSteveGetStructuralRejected SteveGetStructuralError
  deriving (Eq, Show)

verifyOriginalSteveGetStructural
  :: VerifiedSourceSystemsProduction
  -> Either VerifiedSteveGetStructuralError VerifiedSteveGetStructural
verifyOriginalSteveGetStructural production@(VerifiedSourceSystemsProduction
    (SourceSystemsAdmission architecture program _) _ _) = do
  fact <- mapLeft VerifiedSteveGetStructuralRejected
    (verifySteveGetStructural architecture program)
  pure (VerifiedSteveGetStructural production fact)


-- | Private checked *source-qualification envelope*, not a runtime/ABI,
-- fresh allocation, original named proof-use or P9 final authority.
-- The constructor is deliberately not exported. The selected normal source
-- result and the actual canonical PROV-016 claims are rederived together.
data VerifiedSteveGetCanonicalSource = VerifiedSteveGetCanonicalSource
  VerifiedSourceSystemsProduction
  VerifiedSteveGetStructural
  SteveProviderQualifications
  (Set.Set Text)
  deriving (Eq, Show)

data VerifiedSteveGetCanonicalError
  = SteveGetCanonicalQualificationRejected SteveProviderQualificationError
  | SteveGetCanonicalShellRejected Text
  | SteveGetCanonicalPrimitiveMissing Text
  | SteveGetCanonicalEnvironmentMissing
  | SteveGetCanonicalEnvironmentMismatch
  | SteveGetCanonicalMissingSelectedShaProfile
  | SteveGetCanonicalSourceRejected VerifiedSourceSystemsProductionError
  | SteveGetCanonicalStructureRejected VerifiedSteveGetStructuralError
  deriving (Eq, Show)

verifiedSteveGetCanonicalSourceProduction
  :: VerifiedSteveGetCanonicalSource -> VerifiedSourceSystemsProduction
verifiedSteveGetCanonicalSourceProduction
  (VerifiedSteveGetCanonicalSource production _ _ _) = production

-- | Canonical selected provider CONDITION inventory, never a discharge.
-- Includes both SHA-256 and independently selected Blob provider assumptions.
verifiedSteveGetCanonicalSelectedAssumptions
  :: VerifiedSteveGetCanonicalSource -> Set.Set Text
verifiedSteveGetCanonicalSelectedAssumptions
  (VerifiedSteveGetCanonicalSource _ _ _ conditions) = conditions

-- | Re-check the real raw source with a fixed selected SteveGet checker
-- environment, rather than accepting a supplied outcome telescope or
-- a publicly constructible "checked" provider-qualification record.
--
-- This proves only that the *static original source* was checked using the
-- existing canonical Blob/Digest signatures and that their abstract provider
-- qualifications were independently rederived. The actual linked native ABI,
-- stable dynamic owner incarnation and SHA-256 outcome law are still unproved.
produceVerifiedSteveGetCanonicalSource
  :: SourceRootMap
  -> SourceEnvironmentMap
  -> SourceArchitectureRootMap
  -> SourceCoreCorrespondencePolicy
  -> PortableSourceBundle
  -> CoreSystemsProgram
  -> GenericRealizationContext
  -> Either VerifiedSteveGetCanonicalError VerifiedSteveGetCanonicalSource
produceVerifiedSteveGetCanonicalSource roots environments sites policy
    portable program context = do
  qualifications <- mapLeft SteveGetCanonicalQualificationRejected
    materializeSteveProviderQualifications
  let digestConditions = qualificationClaimConditions
        (steveProviderIdentityClaim
          (steveDigestProviderQualification qualifications))
      blobConditions = qualificationClaimConditions
        (steveProviderIdentityClaim
          (steveBlobProviderQualification qualifications))
      selectedConditions = Set.union digestConditions blobConditions
  if Set.member "assumption:sha256-semantic-profile.v1" digestConditions
    then Right ()
    else Left SteveGetCanonicalMissingSelectedShaProfile
  shell <- mapLeft SteveGetCanonicalShellRejected steveGetShellEnvironment
  let selectedNames = Set.fromList ["blob_read", "digest_check"]
      selectedPrimitives =
        Map.restrictKeys (surfacePrimitives shell) selectedNames
  if Map.keysSet selectedPrimitives == selectedNames
    then Right ()
    else case Set.lookupMin
        (Set.difference selectedNames (Map.keysSet selectedPrimitives)) of
      Just missing -> Left (SteveGetCanonicalPrimitiveMissing missing)
      Nothing -> Left (SteveGetCanonicalPrimitiveMissing "unknown")
  let canonical = (emptySurfaceEnvironment emptyStaticContext)
        { surfaceInitialBindings = Map.singleton "contentId"
            (InitialBinding Unrestricted (TyOpaque "ContentId[SHA256]")
              PlainShape)
        , surfacePrimitives = selectedPrimitives
        , surfaceExpectedProvides = Just TyUnit
        , surfaceReleaseTransitions = surfaceReleaseTransitions shell
        }
  actual <- maybe (Left SteveGetCanonicalEnvironmentMissing) Right
    (Map.lookup (DeclarationKey "decl:steve.get") environments)
  if actual == canonical
    then Right ()
    else Left SteveGetCanonicalEnvironmentMismatch
  production <- mapLeft SteveGetCanonicalSourceRejected $
    produceVerifiedSourceSystems
      roots environments sites policy portable program context
  checked <- mapLeft SteveGetCanonicalStructureRejected
    (verifyOriginalSteveGetStructural production)
  Right (VerifiedSteveGetCanonicalSource
    production checked qualifications selectedConditions)


-- | Private selected MODEL-ABI rederivation from the original checked source
-- and admitted Core. Not an attestation of linked machine code, a dynamic
-- source owner, a live source loan or the accepted provider law.
data VerifiedSteveGetModeledABI = VerifiedSteveGetModeledABI
  VerifiedSteveGetCanonicalSource
  RuntimeChoiceABIPlan
  RuntimeChoiceLLVMArtifact
  deriving (Eq, Show)

data VerifiedSteveGetModeledABIError
  = SteveModeledABIBindingRejected RuntimeChoiceSystemsError
  | SteveModeledABICertificationRejected RuntimeChoiceABIError
  | SteveModeledABILoweringRejected RuntimeChoiceLLVMError
  | SteveModeledABIMissingReadSite
  | SteveModeledABIMissingDigestSite
  | SteveModeledABIReadMismatch
  | SteveModeledABIDigestMismatch
  | SteveModeledABILinkedArtifactUnproved
  deriving (Eq, Show)

-- | Recompute from the private source/Core stage instead of taking a supplied
-- ABI certificate or label at face value. For a true P9-F2 proof this modeled
-- result must NEXT be bound to the actual linked native artifact and runtime
-- allocation/loan incarnation through an independently accepted refinement.
verifyOriginalSteveGetModeledABI
  :: VerifiedSteveGetCanonicalSource
  -> RuntimeChoicePayloadPlan
  -> Either VerifiedSteveGetModeledABIError VerifiedSteveGetModeledABI
verifyOriginalSteveGetModeledABI canonical@(VerifiedSteveGetCanonicalSource
    (VerifiedSourceSystemsProduction
      (SourceSystemsAdmission _ core _) originalStage _) _ _ _) payload = do
  stage <- mapLeft SteveModeledABIBindingRejected
    (bindRuntimeChoicePayloadPlan core payload originalStage)
  abi <- mapLeft SteveModeledABICertificationRejected
    (certifyRuntimeChoiceABIPlan core payload stage)
  llvm <- mapLeft SteveModeledABILoweringRejected
    (lowerRuntimeChoiceABIToLLVM phase1RuntimeChoiceLLVMTarget abi stage)
  let sites = runtimeChoiceABISites abi
      readSite = RuntimeChoiceSite "SteveGet" "get.entry"
      checkSite = RuntimeChoiceSite "SteveGet" "get.check"
  readChoice <- maybe (Left SteveModeledABIMissingReadSite) Right
    (Map.lookup readSite sites)
  checkChoice <- maybe (Left SteveModeledABIMissingDigestSite) Right
    (Map.lookup checkSite sites)
  let expectedRead = Map.fromList
        [ ("found", (0, BlockId "get.check",
            Just (ValueId "get.bytes", ABIOwnedBuffer "OwnedBytes")))
        , ("not-found", (1, BlockId "get.not-found", Nothing))
        , ("storage-failure", (2, BlockId "get.failure", Nothing))
        ]
      expectedCheck = Map.fromList
        [ ("accepted", (0, BlockId "get.ok", Nothing))
        , ("rejected", (1, BlockId "get.integrity-failure", Nothing))
        ]
      actualArms choice = Map.map
        (\arm -> (runtimeChoiceABIArmTag arm,
          runtimeChoiceABIArmTarget arm, runtimeChoiceABIArmPayload arm))
        (runtimeChoiceABIArms choice)
      readOk =
        runtimeChoiceABIName readChoice == "BlobProvider.read"
        && runtimeChoiceABIInputs readChoice ==
          [RuntimeChoiceABIInput (ValueId "get.id")
             (ABIRuntimeScalar "ContentId[SHA256]")]
        && actualArms readChoice == expectedRead
      checkOk =
        runtimeChoiceABIName checkChoice == "DigestProvider.check"
        && runtimeChoiceABIInputs checkChoice ==
          [ RuntimeChoiceABIInput (ValueId "get.id")
              (ABIRuntimeScalar "ContentId[SHA256]")
          , RuntimeChoiceABIInput (ValueId "get.bytes-view")
              (ABIBorrowedSlice (ValueId "get.bytes"))
          ]
        && actualArms checkChoice == expectedCheck
  if readOk then Right () else Left SteveModeledABIReadMismatch
  if checkOk then Right () else Left SteveModeledABIDigestMismatch
  pure (VerifiedSteveGetModeledABI canonical abi llvm)
