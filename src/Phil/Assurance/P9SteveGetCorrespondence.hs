{-# LANGUAGE OverloadedStrings #-}
module Phil.Assurance.P9SteveGetCorrespondence
  ( VerifiedSteveGetStructural, VerifiedSteveGetStructuralError (..)
  , verifyOriginalSteveGetStructural
  , VerifiedSteveGetCanonicalSource, VerifiedSteveGetCanonicalError (..)
  , produceVerifiedSteveGetCanonicalSource
  , verifiedSteveGetCanonicalSourceProduction
  , verifiedSteveGetCanonicalSelectedAssumptions
  , VerifiedSteveGetModeledABI, VerifiedSteveGetModeledABIError (..)
  , verifyOriginalSteveGetModeledABI, verifiedSteveGetModeledLLVMText
  , SteveGetLLVMPointerFlowError (..), verifySteveGetLLVMPointerFlow
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler.SourceArchitecture (SourceArchitectureRootMap)
import Phil.Compiler.SourceBundle (SourceRootMap, SourceEnvironmentMap)
import Phil.Compiler.SourceCorePolicy
  ( SteveGetStructuralFact, SteveGetStructuralError, verifySteveGetStructural
  , SourceCoreCorrespondencePolicy )
import qualified Phil.Compiler.SourceSystems as Source
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
import Phil.Core.ProviderQualificationIdentity
  ( ProviderQualificationClaimIdentityInput (..) )
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Ty (..))
import Phil.Examples.Steve.ApplicationShell (steveGetShellEnvironment)
import Phil.Examples.Steve.ProviderQualifications
  ( SteveProviderQualifications (..), SteveProviderQualificationArtifact (..)
  , SteveProviderQualificationError, materializeSteveProviderQualifications )
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceEnvironment (..), SurfaceShape (..)
  , emptySurfaceEnvironment )
import Phil.Surface.Lineage (PortableSourceBundle)
import Phil.Systems.GenericLowering
  ( CoreSystemsProgram, GenericRealizationContext )
import Phil.Systems.IR (ValueId (..), BlockId (..))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

-- | A private, raw-source-rechecked STEVEGET STRUCTURAL discriminator only.
-- This is not a native owner/loan/ABI or P9 final-use certificate.
data VerifiedSteveGetStructural = VerifiedSteveGetStructural
  Source.VerifiedSourceSystemsProduction
  SteveGetStructuralFact
  deriving (Eq, Show)

data VerifiedSteveGetStructuralError
  = VerifiedSteveGetStructuralRejected SteveGetStructuralError
  deriving (Eq, Show)

verifyOriginalSteveGetStructural
  :: Source.VerifiedSourceSystemsProduction
  -> Either VerifiedSteveGetStructuralError VerifiedSteveGetStructural
verifyOriginalSteveGetStructural production = do
  fact <- mapLeft VerifiedSteveGetStructuralRejected $
    Source.withVerifiedSourceCore production verifySteveGetStructural
  pure (VerifiedSteveGetStructural production fact)


-- | Private checked *source-qualification envelope*, not a runtime/ABI,
-- fresh allocation, original named proof-use or P9 final authority.
-- The constructor is deliberately not exported. The selected normal source
-- result and the actual canonical PROV-016 claims are rederived together.
data VerifiedSteveGetCanonicalSource = VerifiedSteveGetCanonicalSource
  Source.VerifiedSourceSystemsProduction
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
  | SteveGetCanonicalSourceRejected Source.VerifiedSourceSystemsProductionError
  | SteveGetCanonicalStructureRejected VerifiedSteveGetStructuralError
  deriving (Eq, Show)

verifiedSteveGetCanonicalSourceProduction
  :: VerifiedSteveGetCanonicalSource -> Source.VerifiedSourceSystemsProduction
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
    Source.produceVerifiedSourceSystems
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

-- | Diagnostic projection of the exact rederived LLVM text, not an
-- independently trusted ABI certificate.
verifiedSteveGetModeledLLVMText :: VerifiedSteveGetModeledABI -> Text
verifiedSteveGetModeledLLVMText
  (VerifiedSteveGetModeledABI _ _ llvm) = runtimeChoiceLLVMText llvm

data VerifiedSteveGetModeledABIError
  = SteveModeledABIBindingRejected RuntimeChoiceSystemsError
  | SteveModeledABICertificationRejected RuntimeChoiceABIError
  | SteveModeledABILoweringRejected RuntimeChoiceLLVMError
  | SteveModeledABIMissingReadSite
  | SteveModeledABIMissingDigestSite
  | SteveModeledABIReadMismatch
  | SteveModeledABIDigestMismatch
  | SteveModeledABILinkedArtifactUnproved
  | SteveModeledABIPointerFlowRejected SteveGetLLVMPointerFlowError
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
    production _ _ _) payload = do
  let core = Source.withVerifiedSourceCore production (\_ value -> value)
      originalStage = Source.verifiedSourceSystemsStage production
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
  mapLeft SteveModeledABIPointerFlowRejected
    (verifySteveGetLLVMPointerFlow (runtimeChoiceLLVMText llvm))
  pure (VerifiedSteveGetModeledABI canonical abi llvm)


-- | This checker deliberately authenticates only the CLOSED, generated
-- SteveGet LLVM pointer flow: read.found payload slot -> get_check load ->
-- digest-check borrowed-owner argument -> release on both successors.
-- It is not a linked-binary verifier, execution trace, or source-loan proof.
data SteveGetLLVMPointerFlowError
  = SteveGetLLVMReadResultSlotMissing
  | SteveGetLLVMPayloadLoadMissing
  | SteveGetLLVMDigestOwnerSubstituted
  | SteveGetLLVMReleaseMissing
  deriving (Eq, Show)

verifySteveGetLLVMPointerFlow
  :: Text -> Either SteveGetLLVMPointerFlowError ()
verifySteveGetLLVMPointerFlow emitted = do
  let readSlot =
        "%phil_runtime_choice_payload_slot_SteveGet_get_entry_get_bytes = alloca ptr"
      readCall =
        "@phil_runtime_choice_SteveGet_get_entry_BlobProvider_read("
      exactReadCall =
        "@phil_runtime_choice_SteveGet_get_entry_BlobProvider_read(ptr %get_id, ptr %phil_runtime_choice_payload_slot_SteveGet_get_entry_get_bytes)"
      payloadLoad =
        "get_check:\n  %get_bytes = load ptr, ptr %phil_runtime_choice_payload_slot_SteveGet_get_entry_get_bytes"
      digestCall =
        "@phil_runtime_choice_SteveGet_get_check_DigestProvider_check(ptr %get_id, ptr %get_bytes)"
      releaseCall = "call void @phil_runtime_release(ptr %get_bytes)"
      count textValue = Text.count textValue emitted
  if count readSlot == 1 && count readCall == 2
       && count exactReadCall == 1
    then Right () else Left SteveGetLLVMReadResultSlotMissing
  if count payloadLoad == 1
    then Right () else Left SteveGetLLVMPayloadLoadMissing
  if count digestCall == 1
    then Right () else Left SteveGetLLVMDigestOwnerSubstituted
  -- Both accepted and rejected cleanup blocks release the SAME load.
  if count releaseCall == 2
    then Right () else Left SteveGetLLVMReleaseMissing
