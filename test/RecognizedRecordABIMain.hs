{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "recognized-record certification closes" certificationPasses
    , test "competing recognized record materialization is rejected" competingMaterializationRejects
    , test "transport exact-receive candidate verifies" exactReceivePasses
    , test "transport exact-receive certification closes" exactReceiveCertificationPasses
    , test "wrong transport parameter identity is rejected" wrongTransportParameterRejects
    , test "wrong exact-receive transport operand is rejected" wrongTransportOperandRejects
    , test "wrong exact-receive payload identity is rejected" wrongPayloadIdentityRejects
    , test "wrong EarlyEOF payload release is rejected" wrongFailureReleaseRejects
    ]
  if and results then pure () else exitFailure

certificationPasses :: Bool
certificationPasses = verifyPhase0RecognizedRecordLLVMCertification == Right ()

competingMaterializationRejects :: Bool
competingMaterializationRejects = case phase0RecognizedRecordBundle of
  Left _ -> False
  Right bundle ->
    let badBundle = addCompetingMaterialization bundle
        badArtifact = lowerSystemsRecognizedRecord
          phase0RecognizedRecordLLVMTarget
          (recognizedRecordArtifact badBundle)
    in case verifyRecognizedRecordTranslation badBundle badArtifact of
      Left (RecognizedRecordSystemsMaterializationSetMismatch _ _ _) -> True
      _ -> False

exactReceivePasses :: Bool
exactReceivePasses = verifyPhase0ExactReceiveLLVM == Right ()

exactReceiveCertificationPasses :: Bool
exactReceiveCertificationPasses = verifyPhase0ExactReceiveLLVMCertification == Right ()

wrongTransportParameterRejects :: Bool
wrongTransportParameterRejects = withExactReceive $ \bundle artifact ->
  let badArtifact = mapLLVMFunction "UploadServer"
        (\function -> function
          { llvmFunctionParameters =
              [LLVMParameter "server.wrong_transport" LLVMPointerParameter]
          })
        artifact
  in case verifyExactReceiveTranslation bundle badArtifact of
    Left (ExactReceiveTransportParameterMismatch "UploadServer" _) -> True
    _ -> False

wrongTransportOperandRejects :: Bool
wrongTransportOperandRejects = withExactReceive $ \bundle artifact ->
  let badArtifact = mapLLVMBlock "UploadServer" (LLVMBlockId "server.payload")
        (mapExactReceive $ \site primitive _ lengthName scalarType payload yes no ->
          LLVMExactReceive site primitive "server.wrong_transport"
            lengthName scalarType payload yes no)
        artifact
  in case verifyExactReceiveTranslation bundle badArtifact of
    Left (ExactReceiveLLVMTerminatorMismatch "UploadServer" _ _) -> True
    _ -> False

wrongPayloadIdentityRejects :: Bool
wrongPayloadIdentityRejects = withExactReceive $ \bundle artifact ->
  let badArtifact = mapLLVMBlock "UploadServer" (LLVMBlockId "server.payload")
        (mapExactReceive $ \site primitive transport lengthName scalarType _ yes no ->
          LLVMExactReceive site primitive transport
            lengthName scalarType "server.wrong_payload" yes no)
        artifact
  in case verifyExactReceiveTranslation bundle badArtifact of
    Left (ExactReceiveLLVMTerminatorMismatch "UploadServer" _ _) -> True
    _ -> False

wrongFailureReleaseRejects :: Bool
wrongFailureReleaseRejects = withExactReceive $ \bundle artifact ->
  let badArtifact = mapLLVMBlock "UploadServer" (LLVMBlockId "server.early_eof")
        (\blockValue -> blockValue
          { llvmBlockOps = map replaceRelease (llvmBlockOps blockValue) })
        artifact
  in case verifyExactReceiveTranslation bundle badArtifact of
    Left (ExactReceiveFailureCleanupMismatch "UploadServer" _ _) -> True
    _ -> False
  where
    replaceRelease operation = case operation of
      LLVMBufferRelease _ -> LLVMBufferRelease "server.wrong_payload"
      other -> other

withExactReceive
  :: (RecognizedRecordBundle -> LLVMArtifact -> Bool)
  -> Bool
withExactReceive action = case phase0RecognizedRecordBundle of
  Left _ -> False
  Right bundle ->
    action bundle (lowerSystemsExactReceive
      phase0ExactReceiveLLVMTarget
      (recognizedRecordArtifact bundle))

mapExactReceive
  :: ( RuntimeSiteRef
    -> Text
    -> Text
    -> Text
    -> ScalarType
    -> Text
    -> LLVMBlockId
    -> LLVMBlockId
    -> LLVMTerminator
     )
  -> LLVMBlock
  -> LLVMBlock
mapExactReceive transform blockValue = blockValue
  { llvmBlockTerminator = case llvmBlockTerminator blockValue of
      LLVMExactReceive site primitive transport lengthName scalarType payload yes no ->
        transform site primitive transport lengthName scalarType payload yes no
      other -> other
  }

mapLLVMFunction :: Text -> (LLVMFunction -> LLVMFunction) -> LLVMArtifact -> LLVMArtifact
mapLLVMFunction functionName transform artifact = artifact
  { llvmArtifactModule = moduleValue
      { llvmFunctions = Map.adjust transform functionName (llvmFunctions moduleValue) }
  }
  where
    moduleValue = llvmArtifactModule artifact

mapLLVMBlock
  :: Text
  -> LLVMBlockId
  -> (LLVMBlock -> LLVMBlock)
  -> LLVMArtifact
  -> LLVMArtifact
mapLLVMBlock functionName blockId transform artifact =
  mapLLVMFunction functionName
    (\function -> function
      { llvmFunctionBlocks = Map.adjust transform blockId (llvmFunctionBlocks function) })
    artifact

addCompetingMaterialization
  :: RecognizedRecordBundle
  -> RecognizedRecordBundle
addCompetingMaterialization bundle = bundle
  { recognizedRecordArtifact = artifact
      { systemsArtifactProgram = program
          { systemsProgramFunctions = Map.adjust
              addToFunction
              functionName
              (systemsProgramFunctions program)
          }
      }
  }
  where
    witness = phase0BeginRecordWitness
    artifact = recognizedRecordArtifact bundle
    program = systemsArtifactProgram artifact
    functionName = recognizedRecordFunction witness
    successBlock = recognizedRecordSuccessBlock witness
    extraId = ValueId "server.begin.competing"
    extraValue = SystemsValue
      { systemsValueId = extraId
      , systemsValueRole = RuntimeRecord (recognizedRecordGrammar witness)
      , systemsStorageIdentity = Nothing
      }
    extraOperation = OpRuntimeCall
      { runtimeCallName = "materialize recognized " <> recognizedRecordGrammar witness
      , runtimeCallInputs = []
      , runtimeCallOutputs = [extraId]
      , runtimeCallSite = Nothing
      , runtimeCallDecision = recognizedRecordMaterializationDecision witness
      }
    addToFunction function = function
      { systemsFunctionValues = Map.insert
          extraId
          extraValue
          (systemsFunctionValues function)
      , systemsFunctionBlocks = Map.adjust
          (\blockValue -> blockValue
            { systemsBlockOps = extraOperation : systemsBlockOps blockValue })
          successBlock
          (systemsFunctionBlocks function)
      }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
