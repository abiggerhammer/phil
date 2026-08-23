{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.VersionSessionChoice
  ( VersionSessionChoiceLLVMError (..)
  , versionSessionChoiceABIDescriptor
  , phase0VersionSessionChoiceLLVMTarget
  , phase0VersionSessionChoiceLLVMArtifact
  , phase0VersionSessionChoiceLLVMVerificationContext
  , lowerSystemsVersionSessionChoice
  , verifyVersionSessionChoiceLLVMWitness
  , verifyVersionSessionChoiceTranslation
  , verifyPhase0VersionSessionChoiceLLVM
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest)
import Phil.LLVM.IR
import Phil.LLVM.PayloadCancelChoice
  ( payloadCancelChoiceABIDescriptor
  , lowerSystemsPayloadCancelChoice
  , phase0PayloadCancelChoiceLLVMTarget
  , verifyPayloadCancelChoiceLLVMWitness
  )
import Phil.LLVM.Verify
import Phil.Systems.IR
import Phil.Systems.LocalRuntimeChoice
import Phil.Systems.VersionChoiceOperands
import Phil.Systems.VersionSessionChoice

data VersionSessionChoiceLLVMError
  = VersionChoiceLLVMSystemsError VersionChoiceOperandsError
  | VersionChoiceLLVMVerificationError LLVMVerificationError
  | VersionChoiceLLVMFunctionMissing Text
  | VersionChoiceLLVMBlockMissing Text LLVMBlockId
  | VersionChoiceLLVMParameterMismatch Text [LLVMParameter]
  | VersionChoiceLLVMHelloProjectionMismatch Text LLVMBlockId [LLVMOp]
  | VersionChoiceLLVMChooserMismatch Text LLVMBlockId LLVMTerminator
  | VersionChoiceLLVMServerSelectMismatch Text LLVMBlockId [LLVMOp]
  | VersionChoiceLLVMClientOfferMismatch Text LLVMBlockId LLVMTerminator
  | VersionChoiceLLVMClientBindingMismatch Text LLVMBlockId [LLVMOp]
  | VersionChoiceLLVMPayloadCancelRegression Text
  | VersionChoiceLLVMRenderedCallMissing Text
  | VersionChoiceLLVMGenericCallDetected Text
  | VersionChoiceLLVMAmbientStateDetected Text
  | VersionChoiceLLVMPoisonDetected Text
  | VersionChoiceLLVMUnresolvedControlDetected Text LLVMBlockId
  deriving (Eq, Show)

versionSessionChoiceABIDescriptor :: Text
versionSessionChoiceABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/version-session-choice-v1"
  , "base-payload-cancel-abi-digest=" <> unDigest (digestText payloadCancelChoiceABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0PayloadCancelChoiceLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0PayloadCancelChoiceLLVMTarget
  , "server-supported=explicit-UploadServer-ptr-parameter"
  , "server-supported-ambient-lookup=forbidden"
  , "hello-versions=phil_record_Hello_get_versions(ptr)->ptr"
  , "choose=phil_runtime_choose_supported(ptr,ptr,ptr)->i1"
  , "choose-arg0=exact-server-supported-versions"
  , "choose-arg1=exact-recognized-Hello.versions"
  , "choose-out=pointer-to-i16-selected-version-slot"
  , "choose-true=some;selected-version-slot-initialized"
  , "choose-false=none;selected-version-slot-not-observed"
  , "choose-provider-obligation=true-value-is-member-of-both-input-sets;false-iff-disjoint"
  , "select-unsupported=phil_runtime_select_unsupported(ptr)->void"
  , "select-version=phil_runtime_select_version(ptr,i16)->void"
  , "receive=phil_runtime_receive_version_choice(ptr,ptr)->i1"
  , "receive-out=pointer-to-i16-selected-version-slot"
  , "wire-unsupported=0x00"
  , "wire-version=0x01 || selected-version-u16-big-endian"
  , "wire-version-size=3-octets"
  , "wire-unsupported-size=1-octet"
  , "receive-0x01=true=version;writes-selected-version"
  , "receive-0x00=false=unsupported;does-not-expose-selected-version"
  , "receive-tag-eof-reserved-or-truncated-version=runtime-must-not-return-normally"
  , "select-write-failure=residual-runtime-assumption;source-select-has-no-failure-edge"
  , "outer-framing=not-defined-by-this-profile"
  , "ambient-choice-state=forbidden"
  , "ambient-version-state=forbidden"
  , "ambient-transport-state=forbidden"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0VersionSessionChoiceLLVMTarget :: LLVMTargetProfile
phase0VersionSessionChoiceLLVMTarget = phase0PayloadCancelChoiceLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText versionSessionChoiceABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/version-session-choice-v1"
  }

phase0VersionSessionChoiceLLVMArtifact
  :: Either VersionChoiceOperandsError LLVMArtifact
phase0VersionSessionChoiceLLVMArtifact = do
  bundle <- phase0VersionChoiceOperandsBundle
  pure (lowerSystemsVersionSessionChoice
    phase0VersionSessionChoiceLLVMTarget
    (versionChoiceOperandsArtifact bundle))

lowerSystemsVersionSessionChoice :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsVersionSessionChoice target systemsArtifact = artifact
  where
    base = lowerSystemsPayloadCancelChoice target systemsArtifact
    versionWitness = phase0VersionSessionChoiceWitness
    operandsWitness = phase0VersionChoiceOperandsWitness
    module0 = llvmArtifactModule base
    module1 = module0
      { llvmFunctions = Map.adjust rewriteServer
          (versionChoiceServerFunction versionWitness) $
          Map.adjust rewriteClient
            (versionChoiceClientFunction versionWitness)
            (llvmFunctions module0)
      }

    rewriteServer function = function
      { llvmFunctionBlocks = Map.adjust rewriteChooser chooserBlockId $
          Map.adjust rewriteUnsupported unsupportedBlockId $
          Map.adjust rewriteVersion versionBlockId (llvmFunctionBlocks function)
      }
    rewriteChooser blockValue = blockValue
      { llvmBlockTerminator = LLVMChooseSupported
          (unValueId (versionOperandsServerSupported operandsWitness))
          (unValueId (versionOperandsHelloVersions operandsWitness))
          (unValueId (versionOperandsSelectedVersion operandsWitness))
          versionBlockId
          unsupportedBlockId
      }
    rewriteUnsupported blockValue = blockValue
      { llvmBlockOps = LLVMUnsupportedSelect
          (unValueId (versionChoiceServerTransport versionWitness))
          : filter (not . isUnloweredSelect (versionChoiceUnsupportedLabel versionWitness))
              (llvmBlockOps blockValue)
      }
    rewriteVersion blockValue = blockValue
      { llvmBlockOps =
          [ LLVMChooseSupportedPayloadBinding
              (unValueId (versionOperandsSelectedVersion operandsWitness))
          , LLVMVersionSelect
              (unValueId (versionChoiceServerTransport versionWitness))
              (unValueId (versionOperandsSelectedVersion operandsWitness))
          ]
          <> filter (not . isUnloweredSelect (versionChoiceVersionLabel versionWitness))
              (llvmBlockOps blockValue)
      }

    rewriteClient function = function
      { llvmFunctionBlocks = Map.adjust rewriteClientOffer clientOfferBlockId $
          Map.adjust rewriteClientVersionTarget clientVersionTargetId
            (llvmFunctionBlocks function)
      }
    rewriteClientOffer blockValue = blockValue
      { llvmBlockTerminator = LLVMVersionChoiceOffer
          (unValueId (versionChoiceClientTransport versionWitness))
          (unValueId (versionChoiceClientSelectedVersion versionWitness))
          clientVersionTargetId
          clientUnsupportedTargetId
      }
    rewriteClientVersionTarget blockValue = blockValue
      { llvmBlockOps = LLVMVersionChoicePayloadBinding
          (unValueId (versionChoiceClientSelectedVersion versionWitness))
          : llvmBlockOps blockValue
      }

    isUnloweredSelect label operation = case operation of
      LLVMPoison description -> description == "unlowered-session-select:" <> label
      _ -> False

    chooserBlockId = LLVMBlockId (unBlockId (versionOperandsChoiceBlock operandsWitness))
    unsupportedBlockId = LLVMBlockId (unBlockId (versionChoiceServerUnsupportedBlock versionWitness))
    versionBlockId = LLVMBlockId (unBlockId (versionChoiceServerVersionBlock versionWitness))
    clientOfferBlockId = LLVMBlockId (unBlockId (versionChoiceClientOfferBlock versionWitness))
    clientVersionTargetId = LLVMBlockId (unBlockId (versionChoiceClientVersionTarget versionWitness))
    clientUnsupportedTargetId = LLVMBlockId (unBlockId (versionChoiceClientUnsupportedTarget versionWitness))

    contract0 = llvmArtifactContract base
    contract1 = contract0 { llvmContractTargetDigest = llvmModuleDigest module1 }
    artifact = base
      { llvmArtifactModule = module1
      , llvmArtifactText = renderLLVMModule module1
      , llvmArtifactContract = contract1
      }

phase0VersionSessionChoiceLLVMVerificationContext
  :: VersionChoiceOperandsBundle
  -> LLVMVerificationContext
phase0VersionSessionChoiceLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = versionChoiceOperandsContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0VersionSessionChoiceLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0VersionSessionChoiceLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0VersionSessionChoiceLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0VersionSessionChoiceLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0VersionSessionChoiceLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0VersionSessionChoiceLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyVersionSessionChoiceTranslation
  :: VersionChoiceOperandsBundle
  -> LLVMArtifact
  -> Either VersionSessionChoiceLLVMError ()
verifyVersionSessionChoiceTranslation bundle llvmArtifact = do
  mapLeft VersionChoiceLLVMSystemsError $ verifyVersionChoiceOperandsBundle bundle
  let systemsArtifact = versionChoiceOperandsArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      moduleValue = llvmArtifactModule llvmArtifact
      context = phase0VersionSessionChoiceLLVMVerificationContext bundle
  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $
    \(functionName, systemsFunction) -> do
      llvmFunction <- lookupLLVMFunction moduleValue functionName
      let expectedParameters =
            [ LLVMParameter (unValueId valueId) LLVMPointerParameter
            | (valueId, SystemsValue { systemsValueRole = role }) <-
                Map.toAscList (systemsFunctionValues systemsFunction)
            , role == TransportHandle || isRuntimeInput role
            ]
      unless (llvmFunctionParameters llvmFunction == expectedParameters) $
        Left (VersionChoiceLLVMParameterMismatch
          functionName (llvmFunctionParameters llvmFunction))
  verifyVersionSessionChoiceLLVMWitness bundle llvmArtifact
  mapLeft VersionChoiceLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsVersionSessionChoice
      context
      systemsArtifact
      llvmArtifact
  where
    isRuntimeInput role = case role of
      RuntimeInput _ -> True
      _ -> False

verifyVersionSessionChoiceLLVMWitness
  :: VersionChoiceOperandsBundle
  -> LLVMArtifact
  -> Either VersionSessionChoiceLLVMError ()
verifyVersionSessionChoiceLLVMWitness bundle llvmArtifact = do
  let versionWitness = phase0VersionSessionChoiceWitness
      operandsWitness = versionChoiceOperandsWitness bundle
      moduleValue = llvmArtifactModule llvmArtifact
      serverName = versionChoiceServerFunction versionWitness
      clientName = versionChoiceClientFunction versionWitness
      helloBlockId = LLVMBlockId (unBlockId (versionOperandsHelloCommitBlock operandsWitness))
      chooserBlockId = LLVMBlockId (unBlockId (versionOperandsChoiceBlock operandsWitness))
      versionBlockId = LLVMBlockId (unBlockId (versionChoiceServerVersionBlock versionWitness))
      unsupportedBlockId = LLVMBlockId (unBlockId (versionChoiceServerUnsupportedBlock versionWitness))
      clientOfferBlockId = LLVMBlockId (unBlockId (versionChoiceClientOfferBlock versionWitness))
      clientVersionTargetId = LLVMBlockId (unBlockId (versionChoiceClientVersionTarget versionWitness))
      clientUnsupportedTargetId = LLVMBlockId (unBlockId (versionChoiceClientUnsupportedTarget versionWitness))
      serverTransport = unValueId (versionChoiceServerTransport versionWitness)
      clientTransport = unValueId (versionChoiceClientTransport versionWitness)
      serverSupported = unValueId (versionOperandsServerSupported operandsWitness)
      helloRecord = unValueId (versionOperandsHelloRecord operandsWitness)
      helloVersions = unValueId (versionOperandsHelloVersions operandsWitness)
      serverSelected = unValueId (versionOperandsSelectedVersion operandsWitness)
      clientSelected = unValueId (versionChoiceClientSelectedVersion versionWitness)

  serverFunction <- lookupLLVMFunction moduleValue serverName
  helloBlock <- lookupLLVMBlock serverName serverFunction helloBlockId
  unless (any (== LLVMOpaqueFieldProjection helloVersions helloRecord "Hello" "versions")
      (llvmBlockOps helloBlock)) $
    Left (VersionChoiceLLVMHelloProjectionMismatch
      serverName helloBlockId (llvmBlockOps helloBlock))

  chooserBlock <- lookupLLVMBlock serverName serverFunction chooserBlockId
  unless (llvmBlockTerminator chooserBlock ==
      LLVMChooseSupported serverSupported helloVersions serverSelected versionBlockId unsupportedBlockId) $
    Left (VersionChoiceLLVMChooserMismatch
      serverName chooserBlockId (llvmBlockTerminator chooserBlock))

  unsupportedBlock <- lookupLLVMBlock serverName serverFunction unsupportedBlockId
  unless (LLVMUnsupportedSelect serverTransport `elem` llvmBlockOps unsupportedBlock) $
    Left (VersionChoiceLLVMServerSelectMismatch
      serverName unsupportedBlockId (llvmBlockOps unsupportedBlock))

  versionBlock <- lookupLLVMBlock serverName serverFunction versionBlockId
  unless
    ( LLVMChooseSupportedPayloadBinding serverSelected `elem` llvmBlockOps versionBlock
    && LLVMVersionSelect serverTransport serverSelected `elem` llvmBlockOps versionBlock
    ) $
    Left (VersionChoiceLLVMServerSelectMismatch
      serverName versionBlockId (llvmBlockOps versionBlock))

  clientFunction <- lookupLLVMFunction moduleValue clientName
  clientOffer <- lookupLLVMBlock clientName clientFunction clientOfferBlockId
  unless (llvmBlockTerminator clientOffer ==
      LLVMVersionChoiceOffer clientTransport clientSelected clientVersionTargetId clientUnsupportedTargetId) $
    Left (VersionChoiceLLVMClientOfferMismatch
      clientName clientOfferBlockId (llvmBlockTerminator clientOffer))
  clientVersion <- lookupLLVMBlock clientName clientFunction clientVersionTargetId
  unless (LLVMVersionChoicePayloadBinding clientSelected `elem` llvmBlockOps clientVersion) $
    Left (VersionChoiceLLVMClientBindingMismatch
      clientName clientVersionTargetId (llvmBlockOps clientVersion))

  let versionPredecessor = versionChoiceOperandsPredecessor bundle
      localPredecessor = versionSessionChoicePredecessor versionPredecessor
      payloadBundle = localRuntimeChoicePredecessor localPredecessor
  case verifyPayloadCancelChoiceLLVMWitness payloadBundle llvmArtifact of
    Right () -> pure ()
    Left err -> Left (VersionChoiceLLVMPayloadCancelRegression (Text.pack (show err)))

  let rendered = llvmArtifactText llvmArtifact
  unless
    ( Text.isInfixOf "declare ptr @phil_record_Hello_get_versions(ptr)" rendered
    && Text.isInfixOf "declare i1 @phil_runtime_choose_supported(ptr, ptr, ptr)" rendered
    && Text.isInfixOf "declare void @phil_runtime_select_unsupported(ptr)" rendered
    && Text.isInfixOf "declare void @phil_runtime_select_version(ptr, i16)" rendered
    && Text.isInfixOf "declare i1 @phil_runtime_receive_version_choice(ptr, ptr)" rendered
    ) $
    Left (VersionChoiceLLVMRenderedCallMissing "version-choice declarations")
  unless
    ( not (Text.isInfixOf "@phil_call_select_unsupported" rendered)
    && not (Text.isInfixOf "@phil_call_select_version" rendered)
    && not (Text.isInfixOf "@phil_call_receive_version_unsupported_label" rendered)
    ) $
    Left (VersionChoiceLLVMGenericCallDetected "version choice")
  unless
    ( not (Text.isInfixOf "@phil_current_supported_versions" rendered)
    && not (Text.isInfixOf "@phil_current_offered_versions" rendered)
    && not (Text.isInfixOf "@phil_current_selected_version" rendered)
    && not (Text.isInfixOf "@phil_current_session_label" rendered)
    && not (Text.isInfixOf "@phil_current_transport" rendered)
    ) $
    Left (VersionChoiceLLVMAmbientStateDetected "version choice")
  unless
    ( not (Text.isInfixOf "unlowered-session-select:version" rendered)
    && not (Text.isInfixOf "unlowered-session-select:unsupported" rendered)
    ) $
    Left (VersionChoiceLLVMPoisonDetected "version choice")
  case llvmBlockTerminator chooserBlock of
    LLVMUnreachable _ -> Left (VersionChoiceLLVMUnresolvedControlDetected serverName chooserBlockId)
    _ -> pure ()
  case llvmBlockTerminator clientOffer of
    LLVMUnreachable _ -> Left (VersionChoiceLLVMUnresolvedControlDetected clientName clientOfferBlockId)
    _ -> pure ()

verifyPhase0VersionSessionChoiceLLVM :: Either VersionSessionChoiceLLVMError ()
verifyPhase0VersionSessionChoiceLLVM = do
  bundle <- mapLeft VersionChoiceLLVMSystemsError phase0VersionChoiceOperandsBundle
  let artifact = lowerSystemsVersionSessionChoice
        phase0VersionSessionChoiceLLVMTarget
        (versionChoiceOperandsArtifact bundle)
  verifyVersionSessionChoiceTranslation bundle artifact

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either VersionSessionChoiceLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName = maybe
  (Left (VersionChoiceLLVMFunctionMissing functionName))
  Right
  (Map.lookup functionName (llvmFunctions moduleValue))

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either VersionSessionChoiceLLVMError LLVMBlock
lookupLLVMBlock functionName function blockId = maybe
  (Left (VersionChoiceLLVMBlockMissing functionName blockId))
  Right
  (Map.lookup blockId (llvmFunctionBlocks function))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform = either (Left . transform) Right
