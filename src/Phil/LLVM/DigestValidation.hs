{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.DigestValidation
  ( DigestValidationLLVMError (..)
  , digestValidationABIDescriptor
  , phase0DigestValidationLLVMTarget
  , phase0DigestValidationLLVMArtifact
  , phase0DigestValidationLLVMVerificationContext
  , verifyDigestValidationTranslation
  , verifyPhase0DigestValidationLLVM
  ) where

import Control.Monad (forM_, unless)
import Data.Char (isAlphaNum)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest, unEvidenceEntryId)
import Phil.LLVM.ExactReceive
  ( exactReceiveABIDescriptor
  , phase0ExactReceiveLLVMTarget
  )
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsDigestValidation)
import Phil.LLVM.Verify
import Phil.Systems.DigestValidation
import Phil.Systems.IR
import Phil.Systems.RecognizedRecord

data DigestValidationLLVMError
  = DigestValidationSystemsCandidateError DigestValidationError
  | DigestValidationLLVMVerificationError LLVMVerificationError
  | DigestValidationLLVMFunctionMissing Text
  | DigestValidationTransportParameterMismatch Text [LLVMParameter]
  | DigestValidationLLVMBlockMissing Text LLVMBlockId
  | DigestValidationRecognitionMismatch Text LLVMBlockId
  | DigestValidationExactReceiveMissing Text ValueId
  | DigestValidationExactReceiveMismatch Text LLVMBlockId LLVMTerminator
  | DigestValidationTerminatorMismatch Text LLVMBlockId LLVMTerminator
  | DigestValidationRenderedCallMismatch Text
  | DigestValidationAmbientStateDetected Text
  | DigestValidationEvidenceSymbolDetected Text
  deriving (Eq, Show)

digestValidationABIDescriptor :: Text
digestValidationABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/digest-validation-v1"
  , "base-exact-receive-abi-digest=" <> unDigest (digestText exactReceiveABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0ExactReceiveLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0ExactReceiveLLVMTarget
  , "transport-handle=component-entry-opaque-ptr"
  , "record-handle=opaque-runtime-owned"
  , "exact-receive-u64=phil_runtime_receive_exact_u64(ptr,i64)->{i8,ptr}"
  , "payload-ssa-name=systems-value-id+.owner"
  , "digest-subjects=recognized-record+borrowed-payload-view"
  , "borrow-erasure=BorrowedSlice(owner)->same-owner-ptr-no-copy"
  , "digest-validator=phil_runtime_digest_validate(ptr,ptr)->i1"
  , "digest-record-operand=exact-recognized-record-handle"
  , "digest-payload-operand=exact-borrow-owner-handle"
  , "digest-success=true,digest-failure=false"
  , "ambient-digest-state=forbidden"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "pointer-strengthening=none-by-default"
  ]

phase0DigestValidationLLVMTarget :: LLVMTargetProfile
phase0DigestValidationLLVMTarget = phase0ExactReceiveLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText digestValidationABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/digest-validation-v1"
  }

phase0DigestValidationLLVMArtifact
  :: Either DigestValidationError LLVMArtifact
phase0DigestValidationLLVMArtifact = do
  bundle <- phase0DigestValidationBundle
  pure (lowerSystemsDigestValidation
    phase0DigestValidationLLVMTarget
    (digestValidationArtifact bundle))

phase0DigestValidationLLVMVerificationContext
  :: DigestValidationBundle
  -> LLVMVerificationContext
phase0DigestValidationLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = digestValidationContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0DigestValidationLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0DigestValidationLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0DigestValidationLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0DigestValidationLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0DigestValidationLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0DigestValidationLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyDigestValidationTranslation
  :: DigestValidationBundle
  -> LLVMArtifact
  -> Either DigestValidationLLVMError ()
verifyDigestValidationTranslation bundle llvmArtifact = do
  mapLeft DigestValidationSystemsCandidateError $
    verifyDigestValidationBundle bundle
  let systemsArtifact = digestValidationArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
      context = phase0DigestValidationLLVMVerificationContext bundle

  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $
    \(functionName, systemsFunction) -> do
      llvmFunction <- lookupLLVMFunction llvmModule functionName
      let expectedParameters =
            [ LLVMParameter (unValueId valueId) LLVMPointerParameter
            | (valueId, SystemsValue { systemsValueRole = TransportHandle }) <-
                Map.toAscList (systemsFunctionValues systemsFunction)
            ]
      unless (llvmFunctionParameters llvmFunction == expectedParameters) $
        Left (DigestValidationTransportParameterMismatch
          functionName
          (llvmFunctionParameters llvmFunction))

  verifyWitness bundle llvmArtifact

  mapLeft DigestValidationLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsDigestValidation
      context
      systemsArtifact
      llvmArtifact

verifyWitness
  :: DigestValidationBundle
  -> LLVMArtifact
  -> Either DigestValidationLLVMError ()
verifyWitness bundle llvmArtifact = do
  let witness = digestValidationWitness bundle
      systemsArtifact = digestValidationArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      functionName = digestValidationFunction witness
      llvmModule = llvmArtifactModule llvmArtifact
  systemsFunction <- case Map.lookup functionName (systemsProgramFunctions systemsProgram) of
    Nothing -> Left (DigestValidationSystemsCandidateError
      (DigestValidationFunctionMissing functionName))
    Just value -> Right value
  llvmFunction <- lookupLLVMFunction llvmModule functionName

  let recognizedWitnesses = recognizedRecordWitnesses
        (digestValidationRecognizedRecordBundle bundle)
  recognizedWitness <- case recognizedWitnesses of
    [value] -> Right value
    _ -> Left (DigestValidationRecognitionMismatch
      functionName
      (LLVMBlockId "server.version"))
  let recognitionBlockId = LLVMBlockId
        (unBlockId (recognizedRecordRecognitionBlock recognizedWitness))
  recognitionBlock <- lookupLLVMBlock functionName llvmFunction recognitionBlockId
  case llvmBlockTerminator recognitionBlock of
    LLVMRecognizeRecord _ grammar record _ _
      | grammar == digestValidationRecordGrammar witness
          && record == unValueId (digestValidationRecord witness) -> pure ()
    _ -> Left (DigestValidationRecognitionMismatch functionName recognitionBlockId)

  payloadReceive <- case
      [ (blockValue, transport, lengthValue, payload, site, yes, no)
      | blockValue <- Map.elems (systemsFunctionBlocks systemsFunction)
      , TermReceiveExact
          { exactTransport = transport
          , exactLength = lengthValue
          , exactPayloadOwner = payload
          , exactSite = site
          , exactSuccess = yes
          , exactFailure = no
          } <- [systemsBlockTerminator blockValue]
      , payload == digestValidationPayloadOwner witness
      ] of
    [entry] -> Right entry
    _ -> Left (DigestValidationExactReceiveMissing
      functionName
      (digestValidationPayloadOwner witness))
  let (sourceReceiveBlock, transportValue, lengthValue, payloadValue, receiveSite, receiveYes, receiveNo) =
        payloadReceive
      receiveBlockId = LLVMBlockId (unBlockId (systemsBlockId sourceReceiveBlock))
      payloadName = payloadSSAName payloadValue
  receiveBlock <- lookupLLVMBlock functionName llvmFunction receiveBlockId
  let expectedReceive = LLVMExactReceive
        receiveSite
        (receivePrimitive systemsFunction lengthValue)
        (unValueId transportValue)
        (unValueId lengthValue)
        (scalarTypeFor systemsFunction lengthValue)
        payloadName
        (LLVMBlockId (unBlockId receiveYes))
        (LLVMBlockId (unBlockId receiveNo))
  unless (llvmBlockTerminator receiveBlock == expectedReceive) $
    Left (DigestValidationExactReceiveMismatch
      functionName receiveBlockId (llvmBlockTerminator receiveBlock))

  digestSourceBlock <- case Map.lookup
      (digestValidationBlock witness)
      (systemsFunctionBlocks systemsFunction) of
    Nothing -> Left (DigestValidationSystemsCandidateError
      (DigestValidationBlockMissing functionName (digestValidationBlock witness)))
    Just value -> Right value
  (digestSite, digestYes, digestNo) <- case systemsBlockTerminator digestSourceBlock of
    TermRuntimeCheck
      { checkInputs = inputs
      , checkSite = site
      , checkSuccess = yes
      , checkFailure = no
      }
      | inputs ==
          [ digestValidationRecord witness
          , digestValidationPayloadView witness
          ]
          && runtimeSiteKind site == DigestBoundary -> Right (site, yes, no)
    other -> Left (DigestValidationSystemsCandidateError
      (DigestValidationCheckMismatch functionName (digestValidationBlock witness) other))

  let digestBlockId = LLVMBlockId (unBlockId (digestValidationBlock witness))
      expectedDigest = LLVMDigestValidate
        digestSite
        (unValueId (digestValidationRecord witness))
        payloadName
        (LLVMBlockId (unBlockId digestYes))
        (LLVMBlockId (unBlockId digestNo))
  digestBlock <- lookupLLVMBlock functionName llvmFunction digestBlockId
  unless (llvmBlockTerminator digestBlock == expectedDigest) $
    Left (DigestValidationTerminatorMismatch
      functionName digestBlockId (llvmBlockTerminator digestBlock))

  let rendered = llvmArtifactText llvmArtifact
      callNeedle =
        "@phil_runtime_digest_validate(ptr %"
          <> symbolish (unValueId (digestValidationRecord witness))
          <> ", ptr %" <> symbolish payloadName <> ")"
      evidenceNamedSymbols =
        [ "@phil_runtime_" <> symbolish (unEvidenceEntryId (runtimeSiteEvidence runtimeSite))
        | sourceFunction <- Map.elems (systemsProgramFunctions systemsProgram)
        , runtimeSite <- runtimeSites sourceFunction
        ]
  unless (Text.isInfixOf callNeedle rendered) $
    Left (DigestValidationRenderedCallMismatch functionName)
  unless
    ( not (Text.isInfixOf "@phil_runtime_digest_validate()" rendered)
    && not (Text.isInfixOf "@phil_current_Begin" rendered)
    && not (Text.isInfixOf "@phil_current_payload" rendered)
    && not (Text.isInfixOf "@phil_current_digest" rendered)
    ) $
    Left (DigestValidationAmbientStateDetected functionName)
  unless (all (not . (`Text.isInfixOf` rendered)) evidenceNamedSymbols) $
    Left (DigestValidationEvidenceSymbolDetected functionName)

lookupLLVMFunction
  :: LLVMModule
  -> Text
  -> Either DigestValidationLLVMError LLVMFunction
lookupLLVMFunction moduleValue functionName =
  case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (DigestValidationLLVMFunctionMissing functionName)
    Just value -> Right value

lookupLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either DigestValidationLLVMError LLVMBlock
lookupLLVMBlock functionName function blockId =
  case Map.lookup blockId (llvmFunctionBlocks function) of
    Nothing -> Left (DigestValidationLLVMBlockMissing functionName blockId)
    Just value -> Right value

payloadSSAName :: ValueId -> Text
payloadSSAName valueId = unValueId valueId <> ".owner"

receivePrimitive :: SystemsFunction -> ValueId -> Text
receivePrimitive function valueId = case scalarTypeFor function valueId of
  ScalarBool -> "receive_exact_bool"
  ScalarUInt width -> "receive_exact_u" <> Text.pack (show width)

scalarTypeFor :: SystemsFunction -> ValueId -> ScalarType
scalarTypeFor function valueId = case Map.lookup valueId (systemsFunctionValues function) of
  Just SystemsValue { systemsValueRole = TypedScalar scalarType } -> scalarType
  _ -> ScalarUInt 0

symbolish :: Text -> Text
symbolish = Text.map (\character -> if isAlphaNum character then character else '_')

verifyPhase0DigestValidationLLVM :: Either DigestValidationLLVMError ()
verifyPhase0DigestValidationLLVM = do
  bundle <- mapLeft DigestValidationSystemsCandidateError phase0DigestValidationBundle
  let systemsArtifact = digestValidationArtifact bundle
      llvmArtifact = lowerSystemsDigestValidation
        phase0DigestValidationLLVMTarget
        systemsArtifact
  verifyDigestValidationTranslation bundle llvmArtifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
