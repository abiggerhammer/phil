{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ExactReceive
  ( ExactReceiveLLVMError (..)
  , exactReceiveABIDescriptor
  , phase0ExactReceiveLLVMTarget
  , phase0ExactReceiveLLVMArtifact
  , phase0ExactReceiveLLVMVerificationContext
  , verifyExactReceiveTranslation
  , verifyPhase0ExactReceiveLLVM
  ) where

import Control.Monad (forM_, unless)
import Data.Char (isAlphaNum)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText, unDigest, unEvidenceEntryId)
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsExactReceive)
import Phil.LLVM.RecognizedRecord
  ( recognizedRecordABIDescriptor
  , phase0RecognizedRecordLLVMTarget
  )
import Phil.LLVM.Verify
import Phil.Systems.IR
import Phil.Systems.RecognizedRecord

data ExactReceiveLLVMError
  = ExactReceiveSystemsCandidateError RecognizedRecordError
  | ExactReceiveLLVMVerificationError LLVMVerificationError
  | ExactReceiveSystemsFunctionMissing Text
  | ExactReceiveLLVMFunctionMissing Text
  | ExactReceiveTransportParameterMismatch Text [LLVMParameter]
  | ExactReceiveSystemsReceiveMissing Text
  | ExactReceiveSystemsReceiveMultiple Text Int
  | ExactReceiveLLVMBlockMissing Text LLVMBlockId
  | ExactReceiveLLVMTerminatorMismatch Text LLVMBlockId LLVMTerminator
  | ExactReceiveFailureBlockMissing Text LLVMBlockId
  | ExactReceiveFailureCleanupMismatch Text LLVMBlockId [LLVMOp]
  | ExactReceiveRecognitionMismatch Text LLVMBlockId
  | ExactReceiveProjectionMismatch Text LLVMBlockId [LLVMOp]
  | ExactReceiveFailClosedStatusMissing Text
  | ExactReceiveAmbientStateDetected Text
  | ExactReceivePhysicalSymbolMismatch Text
  deriving (Eq, Show)

exactReceiveABIDescriptor :: Text
exactReceiveABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/transport-exact-receive-v1"
  , "base-recognized-record-abi-digest=" <> unDigest (digestText recognizedRecordABIDescriptor)
  , "target=" <> llvmTargetTripleName phase0RecognizedRecordLLVMTarget
  , "data-layout=" <> llvmTargetDataLayout phase0RecognizedRecordLLVMTarget
  , "transport-handle=component-entry-opaque-ptr"
  , "session-transition=cfg-typestate-reuses-transport-ptr"
  , "recognition-result={i8,ptr}"
  , "record-handle=opaque-runtime-owned"
  , "scalar-accessor=phil_record_<grammar>_get_<field>(ptr)->iN"
  , "exact-receive-u64=phil_runtime_receive_exact_u64(ptr,i64)->{i8,ptr}"
  , "exact-receive-status=0-early-eof,1-success,other-fail-closed"
  , "exact-receive-payload=opaque-runtime-owned-buffer"
  , "payload-ssa-name=systems-value-id+.owner"
  , "partial-buffer-release=phil_buffer_release(ptr)"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "ambient-transport=forbidden"
  , "pointer-strengthening=none-by-default"
  ]

phase0ExactReceiveLLVMTarget :: LLVMTargetProfile
phase0ExactReceiveLLVMTarget = phase0RecognizedRecordLLVMTarget
  { llvmTargetRuntimeABIDigest = digestText exactReceiveABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/transport-exact-receive-v1"
  }

phase0ExactReceiveLLVMArtifact :: Either RecognizedRecordError LLVMArtifact
phase0ExactReceiveLLVMArtifact = do
  bundle <- phase0RecognizedRecordBundle
  pure (lowerSystemsExactReceive
    phase0ExactReceiveLLVMTarget
    (recognizedRecordArtifact bundle))

phase0ExactReceiveLLVMVerificationContext
  :: RecognizedRecordBundle
  -> LLVMVerificationContext
phase0ExactReceiveLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = recognizedRecordContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0ExactReceiveLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0ExactReceiveLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0ExactReceiveLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0ExactReceiveLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0ExactReceiveLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0ExactReceiveLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyExactReceiveTranslation
  :: RecognizedRecordBundle
  -> LLVMArtifact
  -> Either ExactReceiveLLVMError ()
verifyExactReceiveTranslation bundle llvmArtifact = do
  mapLeft ExactReceiveSystemsCandidateError (verifyRecognizedRecordBundle bundle)
  let systemsArtifact = recognizedRecordArtifact bundle
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
      context = phase0ExactReceiveLLVMVerificationContext bundle

  forM_ (Map.toAscList (systemsProgramFunctions systemsProgram)) $ \(functionName, systemsFunction) -> do
    llvmFunction <- case Map.lookup functionName (llvmFunctions llvmModule) of
      Nothing -> Left (ExactReceiveLLVMFunctionMissing functionName)
      Just value -> Right value
    let expectedParameters =
          [ LLVMParameter (unValueId valueId) LLVMPointerParameter
          | (valueId, SystemsValue { systemsValueRole = TransportHandle }) <-
              Map.toAscList (systemsFunctionValues systemsFunction)
          ]
    unless (llvmFunctionParameters llvmFunction == expectedParameters) $
      Left (ExactReceiveTransportParameterMismatch
        functionName
        (llvmFunctionParameters llvmFunction))

  forM_ (recognizedRecordWitnesses bundle) $ \witness ->
    verifyWitness systemsArtifact llvmArtifact witness

  mapLeft ExactReceiveLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsExactReceive
      context
      systemsArtifact
      llvmArtifact

verifyWitness
  :: SystemsArtifact
  -> LLVMArtifact
  -> RecognizedRecordWitness
  -> Either ExactReceiveLLVMError ()
verifyWitness systemsArtifact llvmArtifact witness = do
  let functionName = recognizedRecordFunction witness
      systemsProgram = systemsArtifactProgram systemsArtifact
      llvmModule = llvmArtifactModule llvmArtifact
  systemsFunction <- case Map.lookup functionName (systemsProgramFunctions systemsProgram) of
    Nothing -> Left (ExactReceiveSystemsFunctionMissing functionName)
    Just value -> Right value
  llvmFunction <- case Map.lookup functionName (llvmFunctions llvmModule) of
    Nothing -> Left (ExactReceiveLLVMFunctionMissing functionName)
    Just value -> Right value

  let recognitionBlockId = LLVMBlockId
        (unBlockId (recognizedRecordRecognitionBlock witness))
  recognitionBlock <- case Map.lookup recognitionBlockId (llvmFunctionBlocks llvmFunction) of
    Nothing -> Left (ExactReceiveLLVMBlockMissing functionName recognitionBlockId)
    Just value -> Right value
  case llvmBlockTerminator recognitionBlock of
    LLVMRecognizeRecord _ grammar record _ _
      | grammar == recognizedRecordGrammar witness
          && record == unValueId (recognizedRecordValue witness) -> pure ()
    _ -> Left (ExactReceiveRecognitionMismatch functionName recognitionBlockId)

  let projectionBlockId = LLVMBlockId
        (unBlockId (recognizedRecordSuccessBlock witness))
  projectionBlock <- case Map.lookup projectionBlockId (llvmFunctionBlocks llvmFunction) of
    Nothing -> Left (ExactReceiveLLVMBlockMissing functionName projectionBlockId)
    Just value -> Right value
  let matchingProjections =
        [ operation
        | operation@(LLVMFieldProjection output record grammar fieldName scalarType) <-
            llvmBlockOps projectionBlock
        , output == unValueId (recognizedRecordProjectionOutput witness)
        , record == unValueId (recognizedRecordValue witness)
        , grammar == recognizedRecordGrammar witness
        , fieldName == recognizedRecordField witness
        , scalarType == recognizedRecordProjectionType witness
        ]
  unless (length matchingProjections == 1) $
    Left (ExactReceiveProjectionMismatch functionName projectionBlockId matchingProjections)

  let exactReceives =
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
        , lengthValue == recognizedRecordProjectionOutput witness
        ]
  (sourceBlock, transportValue, lengthValue, payloadValue, site, yes, no) <-
    case exactReceives of
      [] -> Left (ExactReceiveSystemsReceiveMissing functionName)
      [entry] -> Right entry
      many -> Left (ExactReceiveSystemsReceiveMultiple functionName (length many))

  let receiveBlockId = LLVMBlockId (unBlockId (systemsBlockId sourceBlock))
      payloadName = payloadSSAName payloadValue
  receiveBlock <- case Map.lookup receiveBlockId (llvmFunctionBlocks llvmFunction) of
    Nothing -> Left (ExactReceiveLLVMBlockMissing functionName receiveBlockId)
    Just value -> Right value
  let expectedTerminator = LLVMExactReceive
        site
        ("receive_exact_" <> scalarSuffix (recognizedRecordProjectionType witness))
        (unValueId transportValue)
        (unValueId lengthValue)
        (recognizedRecordProjectionType witness)
        payloadName
        (LLVMBlockId (unBlockId yes))
        (LLVMBlockId (unBlockId no))
  unless (llvmBlockTerminator receiveBlock == expectedTerminator) $
    Left (ExactReceiveLLVMTerminatorMismatch
      functionName receiveBlockId (llvmBlockTerminator receiveBlock))

  let failureBlockId = LLVMBlockId (unBlockId no)
  failureBlock <- case Map.lookup failureBlockId (llvmFunctionBlocks llvmFunction) of
    Nothing -> Left (ExactReceiveFailureBlockMissing functionName failureBlockId)
    Just value -> Right value
  let releases =
        [ operation
        | operation@(LLVMBufferRelease owner) <- llvmBlockOps failureBlock
        , owner == payloadName
        ]
  unless (releases == [LLVMBufferRelease payloadName]) $
    Left (ExactReceiveFailureCleanupMismatch
      functionName failureBlockId (llvmBlockOps failureBlock))

  let rendered = llvmArtifactText llvmArtifact
      blockSymbol = symbolish (unBlockId (systemsBlockId sourceBlock))
      statusNeedle =
        "icmp eq i8 %phil_exact_receive_status_" <> blockSymbol <> ", 1"
      receiveNeedle =
        "@phil_runtime_receive_exact_" <> scalarSuffix (recognizedRecordProjectionType witness)
          <> "(ptr %" <> symbolish (unValueId transportValue)
          <> ", " <> renderScalarTypeLocal (recognizedRecordProjectionType witness)
          <> " %" <> symbolish (unValueId lengthValue) <> ")"
      releaseNeedle =
        "@phil_buffer_release(ptr %" <> symbolish payloadName <> ")"
      evidenceNamedSymbols =
        [ "@phil_runtime_" <> symbolish (unEvidenceEntryId (runtimeSiteEvidence runtimeSite))
        | sourceFunction <- Map.elems (systemsProgramFunctions systemsProgram)
        , runtimeSite <- runtimeSites sourceFunction
        ]
  unless (Text.isInfixOf statusNeedle rendered) $
    Left (ExactReceiveFailClosedStatusMissing functionName)
  unless
    ( Text.isInfixOf receiveNeedle rendered
    && Text.isInfixOf releaseNeedle rendered
    && all (not . (`Text.isInfixOf` rendered)) evidenceNamedSymbols
    ) $
    Left (ExactReceivePhysicalSymbolMismatch functionName)
  unless
    ( not (Text.isInfixOf "@phil_current_transport" rendered)
    && not (Text.isInfixOf "@phil_current_payload" rendered)
    && not (Text.isInfixOf "@phil_runtime_receive_exact_u64(i64" rendered)
    ) $
    Left (ExactReceiveAmbientStateDetected functionName)

payloadSSAName :: ValueId -> Text
payloadSSAName valueId = unValueId valueId <> ".owner"

scalarSuffix :: ScalarType -> Text
scalarSuffix scalarType = case scalarType of
  ScalarBool -> "bool"
  ScalarUInt width -> "u" <> Text.pack (show width)

renderScalarTypeLocal :: ScalarType -> Text
renderScalarTypeLocal scalarType = case scalarType of
  ScalarBool -> "i1"
  ScalarUInt width -> "i" <> Text.pack (show width)

symbolish :: Text -> Text
symbolish = Text.map (\character -> if isAlphaNum character then character else '_')

verifyPhase0ExactReceiveLLVM :: Either ExactReceiveLLVMError ()
verifyPhase0ExactReceiveLLVM = do
  bundle <- mapLeft ExactReceiveSystemsCandidateError phase0RecognizedRecordBundle
  let systemsArtifact = recognizedRecordArtifact bundle
      llvmArtifact = lowerSystemsExactReceive phase0ExactReceiveLLVMTarget systemsArtifact
  verifyExactReceiveTranslation bundle llvmArtifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
