{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.RecognizedRecord
  ( RecognizedRecordLLVMError (..)
  , recognizedRecordABIDescriptor
  , phase0RecognizedRecordLLVMTarget
  , phase0RecognizedRecordLLVMArtifact
  , phase0RecognizedRecordLLVMVerificationContext
  , verifyRecognizedRecordTranslation
  , verifyPhase0RecognizedRecordLLVM
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (digestText)
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsRecognizedRecord)
import Phil.LLVM.Phase0 (phase0LLVMTarget)
import Phil.LLVM.Verify
import Phil.Systems.IR
import Phil.Systems.RecognizedRecord

data RecognizedRecordLLVMError
  = RecognizedRecordSystemsCandidateError RecognizedRecordError
  | RecognizedRecordLLVMVerificationError LLVMVerificationError
  | RecognizedRecordSystemsFunctionMissing Text
  | RecognizedRecordSystemsSuccessBlockMissing Text BlockId
  | RecognizedRecordSystemsMaterializationSetMismatch
      Text BlockId [(ValueId, Text, DecisionId)]
  | RecognizedRecordLLVMFunctionMissing Text
  | RecognizedRecordLLVMRecognitionBlockMissing Text LLVMBlockId
  | RecognizedRecordLLVMRecognitionMismatch Text LLVMBlockId
  | RecognizedRecordLLVMSuccessBlockMissing Text LLVMBlockId
  | RecognizedRecordLLVMProjectionMismatch Text LLVMBlockId [LLVMOp]
  | RecognizedRecordSystemsExactReceiveMissing Text ValueId
  | RecognizedRecordSystemsExactReceiveMultiple Text ValueId Int
  | RecognizedRecordLLVMExactReceiveBlockMissing Text LLVMBlockId
  | RecognizedRecordLLVMExactReceiveMismatch Text LLVMBlockId LLVMTerminator
  | RecognizedRecordLLVMFailClosedStatusMissing Text
  | RecognizedRecordLLVMPhysicalSymbolMismatch Text
  deriving (Eq, Show)

recognizedRecordABIDescriptor :: Text
recognizedRecordABIDescriptor = Text.unlines
  [ "phil-runtime/phase0/recognized-record-v1"
  , "target=x86_64-unknown-linux-gnu"
  , "recognition-result={i8,ptr}"
  , "recognition-status=0-failure,1-success,other-fail-closed"
  , "recognition-failure-record=null"
  , "record-handle=opaque-runtime-owned"
  , "generated-record-dereference=forbidden"
  , "scalar-accessor=phil_record_<grammar>_get_<field>(ptr)->iN"
  , "runtime-symbol-identity=physical-primitive-and-signature"
  , "exact-receive-u64=phil_runtime_receive_exact_u64(i64)->i1"
  , "pointer-strengthening=none-by-default"
  ]

phase0RecognizedRecordLLVMTarget :: LLVMTargetProfile
phase0RecognizedRecordLLVMTarget = phase0LLVMTarget
  { llvmTargetRuntimeABIDigest = digestText recognizedRecordABIDescriptor
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/recognized-record-v1"
  }

phase0RecognizedRecordLLVMArtifact
  :: Either RecognizedRecordError LLVMArtifact
phase0RecognizedRecordLLVMArtifact = do
  bundle <- phase0RecognizedRecordBundle
  pure (lowerSystemsRecognizedRecord
    phase0RecognizedRecordLLVMTarget
    (recognizedRecordArtifact bundle))

phase0RecognizedRecordLLVMVerificationContext
  :: RecognizedRecordBundle
  -> LLVMVerificationContext
phase0RecognizedRecordLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = recognizedRecordContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0RecognizedRecordLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0RecognizedRecordLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0RecognizedRecordLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0RecognizedRecordLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0RecognizedRecordLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0RecognizedRecordLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

-- | Validate the recognized-record relation independently of the lowering
-- producer's pattern matching.  The generic LLVM verifier still checks the
-- complete artifact; these checks specifically bind the target record handle,
-- field accessor and exact-receive scalar argument back to the Systems witness.
verifyRecognizedRecordTranslation
  :: RecognizedRecordBundle
  -> LLVMArtifact
  -> Either RecognizedRecordLLVMError ()
verifyRecognizedRecordTranslation bundle llvmArtifact = do
  let systemsArtifact = recognizedRecordArtifact bundle
      context = phase0RecognizedRecordLLVMVerificationContext bundle
  mapLeft RecognizedRecordLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsRecognizedRecord
      context
      systemsArtifact
      llvmArtifact
  forM_ (recognizedRecordWitnesses bundle) $ \witness ->
    verifyWitnessTranslation systemsArtifact llvmArtifact witness

verifyWitnessTranslation
  :: SystemsArtifact
  -> LLVMArtifact
  -> RecognizedRecordWitness
  -> Either RecognizedRecordLLVMError ()
verifyWitnessTranslation systemsArtifact llvmArtifact witness = do
  let systemsProgram = systemsArtifactProgram systemsArtifact
      functionName = recognizedRecordFunction witness
  systemsFunction <- case Map.lookup functionName (systemsProgramFunctions systemsProgram) of
    Nothing -> Left (RecognizedRecordSystemsFunctionMissing functionName)
    Just value -> Right value
  successBlock <- case Map.lookup
      (recognizedRecordSuccessBlock witness)
      (systemsFunctionBlocks systemsFunction) of
    Nothing -> Left (RecognizedRecordSystemsSuccessBlockMissing
      functionName
      (recognizedRecordSuccessBlock witness))
    Just value -> Right value
  let materializations = recognizedMaterializations systemsFunction successBlock
      expectedMaterializations =
        [ ( recognizedRecordValue witness
          , recognizedRecordGrammar witness
          , recognizedRecordMaterializationDecision witness
          )
        ]
  unless (materializations == expectedMaterializations) $
    Left (RecognizedRecordSystemsMaterializationSetMismatch
      functionName
      (recognizedRecordSuccessBlock witness)
      materializations)

  sourceRecognitionBlock <- case Map.lookup
      (recognizedRecordRecognitionBlock witness)
      (systemsFunctionBlocks systemsFunction) of
    Nothing -> Left (RecognizedRecordSystemsFunctionMissing functionName)
    Just value -> Right value
  (recognitionSite, recognitionSuccess, recognitionFailure) <-
    case systemsBlockTerminator sourceRecognitionBlock of
      TermRecognize
        { recognizeSite = site
        , recognizeSuccess = yes
        , recognizeFailure = no
        } -> Right (site, yes, no)
      _ -> Left (RecognizedRecordLLVMRecognitionMismatch
        functionName
        (LLVMBlockId (unBlockId (recognizedRecordRecognitionBlock witness))))

  llvmFunction <- case Map.lookup
      functionName
      (llvmFunctions (llvmArtifactModule llvmArtifact)) of
    Nothing -> Left (RecognizedRecordLLVMFunctionMissing functionName)
    Just value -> Right value
  let llvmRecognitionBlockId = LLVMBlockId
        (unBlockId (recognizedRecordRecognitionBlock witness))
  llvmRecognitionBlock <- case Map.lookup
      llvmRecognitionBlockId
      (llvmFunctionBlocks llvmFunction) of
    Nothing -> Left (RecognizedRecordLLVMRecognitionBlockMissing
      functionName llvmRecognitionBlockId)
    Just value -> Right value
  case llvmBlockTerminator llvmRecognitionBlock of
    LLVMRecognizeRecord site grammar record yes no
      | site == recognitionSite
          && grammar == recognizedRecordGrammar witness
          && record == unValueId (recognizedRecordValue witness)
          && yes == LLVMBlockId (unBlockId recognitionSuccess)
          && no == LLVMBlockId (unBlockId recognitionFailure) -> pure ()
    _ -> Left (RecognizedRecordLLVMRecognitionMismatch
      functionName llvmRecognitionBlockId)

  let llvmSuccessBlockId = LLVMBlockId
        (unBlockId (recognizedRecordSuccessBlock witness))
  llvmSuccessBlock <- case Map.lookup
      llvmSuccessBlockId
      (llvmFunctionBlocks llvmFunction) of
    Nothing -> Left (RecognizedRecordLLVMSuccessBlockMissing
      functionName llvmSuccessBlockId)
    Just value -> Right value
  let projections =
        [ operation
        | operation@LLVMFieldProjection
            { } <- llvmBlockOps llvmSuccessBlock
        , projectionTouchesWitness witness operation
        ]
      expectedProjection = LLVMFieldProjection
        (unValueId (recognizedRecordProjectionOutput witness))
        (unValueId (recognizedRecordValue witness))
        (recognizedRecordGrammar witness)
        (recognizedRecordField witness)
        (recognizedRecordProjectionType witness)
  unless (projections == [expectedProjection]) $
    Left (RecognizedRecordLLVMProjectionMismatch
      functionName llvmSuccessBlockId projections)

  exactReceives <- pure
    [ (blockValue, site, yes, no)
    | blockValue <- Map.elems (systemsFunctionBlocks systemsFunction)
    , TermReceiveExact
        { exactLength = lengthValue
        , exactSite = site
        , exactSuccess = yes
        , exactFailure = no
        } <- [systemsBlockTerminator blockValue]
    , lengthValue == recognizedRecordProjectionOutput witness
    ]
  (sourceReceiveBlock, receiveSite, receiveSuccess, receiveFailure) <-
    case exactReceives of
      [] -> Left (RecognizedRecordSystemsExactReceiveMissing
        functionName
        (recognizedRecordProjectionOutput witness))
      [entry] -> Right entry
      many -> Left (RecognizedRecordSystemsExactReceiveMultiple
        functionName
        (recognizedRecordProjectionOutput witness)
        (length many))
  let llvmReceiveBlockId = LLVMBlockId (unBlockId (systemsBlockId sourceReceiveBlock))
  llvmReceiveBlock <- case Map.lookup
      llvmReceiveBlockId
      (llvmFunctionBlocks llvmFunction) of
    Nothing -> Left (RecognizedRecordLLVMExactReceiveBlockMissing
      functionName llvmReceiveBlockId)
    Just value -> Right value
  let expectedPrimitive = "receive_exact_" <> scalarSuffix
        (recognizedRecordProjectionType witness)
      expectedReceive = LLVMRuntimeScalarBranch
        receiveSite
        expectedPrimitive
        (unValueId (recognizedRecordProjectionOutput witness))
        (recognizedRecordProjectionType witness)
        (LLVMBlockId (unBlockId receiveSuccess))
        (LLVMBlockId (unBlockId receiveFailure))
  unless (llvmBlockTerminator llvmReceiveBlock == expectedReceive) $
    Left (RecognizedRecordLLVMExactReceiveMismatch
      functionName
      llvmReceiveBlockId
      (llvmBlockTerminator llvmReceiveBlock))

  let rendered = llvmArtifactText llvmArtifact
      recognitionStatusNeedle =
        "icmp eq i8 %phil_recognition_status_"
          <> symbolish (unBlockId (recognizedRecordRecognitionBlock witness))
          <> ", 1"
  unless (Text.isInfixOf recognitionStatusNeedle rendered) $
    Left (RecognizedRecordLLVMFailClosedStatusMissing functionName)
  unless
    ( Text.isInfixOf
        ("@phil_runtime_recognize_" <> symbolish (recognizedRecordGrammar witness))
        rendered
    && Text.isInfixOf
        ("@phil_record_" <> symbolish (recognizedRecordGrammar witness)
          <> "_get_" <> symbolish (recognizedRecordField witness))
        rendered
    && Text.isInfixOf
        ("@phil_runtime_" <> symbolish expectedPrimitive)
        rendered
    && not (Text.isInfixOf "@phil_runtime_evidence_" rendered)
    && not (Text.isInfixOf "@phil_current_" rendered)
    ) $
    Left (RecognizedRecordLLVMPhysicalSymbolMismatch functionName)

recognizedMaterializations
  :: SystemsFunction
  -> SystemsBlock
  -> [(ValueId, Text, DecisionId)]
recognizedMaterializations function blockValue =
  [ (output, grammar, decisionId)
  | OpRuntimeCall
      { runtimeCallName = name
      , runtimeCallInputs = []
      , runtimeCallOutputs = [output]
      , runtimeCallSite = Nothing
      , runtimeCallDecision = decisionId
      } <- systemsBlockOps blockValue
  , Just SystemsValue { systemsValueRole = RuntimeRecord grammar } <-
      [Map.lookup output (systemsFunctionValues function)]
  , name == "materialize recognized " <> grammar
  ]

projectionTouchesWitness :: RecognizedRecordWitness -> LLVMOp -> Bool
projectionTouchesWitness witness operation = case operation of
  LLVMFieldProjection output record grammar _ _ ->
    output == unValueId (recognizedRecordProjectionOutput witness)
      || record == unValueId (recognizedRecordValue witness)
      || grammar == recognizedRecordGrammar witness
  _ -> False

scalarSuffix :: ScalarType -> Text
scalarSuffix scalarType = case scalarType of
  ScalarBool -> "bool"
  ScalarUInt width -> "u" <> Text.pack (show width)

-- Keep this deliberately local to the ABI validator so checks of rendered
-- linker-visible names do not depend on the producer's private renderer helper.
symbolish :: Text -> Text
symbolish = Text.map (\character ->
  if character == '.' || character == '-' || character == ' '
    then '_'
    else character)

verifyPhase0RecognizedRecordLLVM
  :: Either RecognizedRecordLLVMError ()
verifyPhase0RecognizedRecordLLVM = do
  bundle <- mapLeft RecognizedRecordSystemsCandidateError phase0RecognizedRecordBundle
  let systemsArtifact = recognizedRecordArtifact bundle
      llvmArtifact = lowerSystemsRecognizedRecord phase0RecognizedRecordLLVMTarget systemsArtifact
  verifyRecognizedRecordTranslation bundle llvmArtifact

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
