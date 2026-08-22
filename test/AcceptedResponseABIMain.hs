{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "accepted-response Systems witness verifies" systemsCandidatePasses
    , test "accepted-response LLVM candidate verifies" llvmCandidatePasses
    , test "accepted-response certification closes" certificationPasses
    , test "accepted-response ABI binds exact 17-octet wire payload" wireDescriptorBound
    , test "accepted-response ABI keeps outer framing separate" framingDescriptorBound
    , test "accepted-response ABI records residual write-failure boundary" writeFailureDescriptorBound
    , test "accepted-response ABI does not invent UploadId freshness" freshnessDescriptorBound
    , test "wrong Systems accepted transport is rejected" wrongSystemsTransportRejects
    , test "wrong Systems accepted UploadId is rejected" wrongSystemsUploadIdRejects
    , test "duplicate Systems accepted UploadId use is rejected" duplicateSystemsUseRejects
    , test "wrong LLVM accepted transport is rejected" wrongLLVMTransportRejects
    , test "wrong LLVM accepted UploadId is rejected" wrongLLVMUploadIdRejects
    , test "generic nullary accepted call is rejected" genericAcceptedCallRejects
    , test "generated UploadId layout access is rejected" uploadIdLayoutRejects
    ]
  if and results then pure () else exitFailure

systemsCandidatePasses :: Bool
systemsCandidatePasses = case phase0AcceptedResponseBundle of
  Right _ -> True
  Left _ -> False

llvmCandidatePasses :: Bool
llvmCandidatePasses = verifyPhase0AcceptedResponseLLVM == Right ()

certificationPasses :: Bool
certificationPasses = verifyPhase0AcceptedResponseLLVMCertification == Right ()

wireDescriptorBound :: Bool
wireDescriptorBound = all (`Text.isInfixOf` acceptedResponseABIDescriptor)
  [ "accepted-wire-length=17-octets"
  , "accepted-wire-tag=0x01"
  , "rejected-wire-tag-reserved=0x00"
  , "upload-id-wire-token=16-octets"
  , "upload-id-wire-token-authority=runtime-encoder-only"
  ]

framingDescriptorBound :: Bool
framingDescriptorBound =
  Text.isInfixOf
    "accepted-outer-framing=not-defined-by-this-profile"
    acceptedResponseABIDescriptor

writeFailureDescriptorBound :: Bool
writeFailureDescriptorBound =
  Text.isInfixOf
    "accepted-write-failure=residual-runtime-assumption-no-source-failure-edge"
    acceptedResponseABIDescriptor

freshnessDescriptorBound :: Bool
freshnessDescriptorBound =
  Text.isInfixOf
    "upload-id-freshness-or-uniqueness=not-certified-by-this-profile"
    acceptedResponseABIDescriptor

wrongSystemsTransportRejects :: Bool
wrongSystemsTransportRejects = withAcceptedBundle $ \bundle ->
  let witness = acceptedResponseWitness bundle
      storeWitness = storageWitness (acceptedResponseStorageBundle bundle)
      badArtifact = mapSystemsBlock
        (acceptedResponseFunction witness)
        (acceptedResponseBlock witness)
        (mapAcceptedOp $ \operation -> operation
          { runtimeCallInputs =
              [ValueId "server.frame.begin", acceptedResponseUploadId witness] })
        (acceptedResponseArtifact bundle)
  in case verifyAcceptedResponseWitness badArtifact storeWitness witness of
    Left AcceptedResponseOperationMismatch {} -> True
    _ -> False

wrongSystemsUploadIdRejects :: Bool
wrongSystemsUploadIdRejects = withAcceptedBundle $ \bundle ->
  let witness = acceptedResponseWitness bundle
      storeWitness = storageWitness (acceptedResponseStorageBundle bundle)
      badArtifact = mapSystemsBlock
        (acceptedResponseFunction witness)
        (acceptedResponseBlock witness)
        (mapAcceptedOp $ \operation -> operation
          { runtimeCallInputs =
              [acceptedResponseTransport witness, ValueId "server.payload_choice"] })
        (acceptedResponseArtifact bundle)
  in case verifyAcceptedResponseWitness badArtifact storeWitness witness of
    Left AcceptedResponseOperationMismatch {} -> True
    _ -> False

duplicateSystemsUseRejects :: Bool
duplicateSystemsUseRejects = withAcceptedBundle $ \bundle ->
  let witness = acceptedResponseWitness bundle
      storeWitness = storageWitness (acceptedResponseStorageBundle bundle)
      badArtifact = mapSystemsBlock
        (acceptedResponseFunction witness)
        (acceptedResponseBlock witness)
        (\blockValue -> blockValue
          { systemsBlockOps = systemsBlockOps blockValue <> systemsBlockOps blockValue })
        (acceptedResponseArtifact bundle)
  in case verifyAcceptedResponseWitness badArtifact storeWitness witness of
    Left AcceptedResponseOperationMismatch {} -> True
    Left AcceptedResponseUploadIdUseCountMismatch {} -> True
    _ -> False

wrongLLVMTransportRejects :: Bool
wrongLLVMTransportRejects = withAcceptedLLVM $ \bundle artifact ->
  let witness = acceptedResponseWitness bundle
      badArtifact = mapLLVMBlock
        (acceptedResponseFunction witness)
        (LLVMBlockId (unBlockId (acceptedResponseBlock witness)))
        (mapAcceptedLLVM $ \_ uploadId ->
          LLVMAcceptedResponse "server.wrong_transport" uploadId)
        artifact
  in case verifyAcceptedResponseTranslation bundle badArtifact of
    Left AcceptedResponseLLVMOperationMismatch {} -> True
    _ -> False

wrongLLVMUploadIdRejects :: Bool
wrongLLVMUploadIdRejects = withAcceptedLLVM $ \bundle artifact ->
  let witness = acceptedResponseWitness bundle
      badArtifact = mapLLVMBlock
        (acceptedResponseFunction witness)
        (LLVMBlockId (unBlockId (acceptedResponseBlock witness)))
        (mapAcceptedLLVM $ \transport _ ->
          LLVMAcceptedResponse transport "server.wrong_upload_id")
        artifact
  in case verifyAcceptedResponseTranslation bundle badArtifact of
    Left AcceptedResponseLLVMOperationMismatch {} -> True
    _ -> False

genericAcceptedCallRejects :: Bool
genericAcceptedCallRejects = withAcceptedLLVM $ \bundle artifact ->
  let badArtifact = artifact
        { llvmArtifactText = llvmArtifactText artifact
            <> "\ndeclare void @phil_call_select_accepted()\n" }
  in case verifyAcceptedResponseTranslation bundle badArtifact of
    Left AcceptedResponseGenericCallDetected {} -> True
    _ -> False

uploadIdLayoutRejects :: Bool
uploadIdLayoutRejects = withAcceptedLLVM $ \bundle artifact ->
  let badArtifact = artifact
        { llvmArtifactText = llvmArtifactText artifact
            <> "\n%phil_bad_id_byte = load i8, ptr %server_upload_id\n" }
  in case verifyAcceptedResponseTranslation bundle badArtifact of
    Left AcceptedResponseUploadIdRepresentationViolation {} -> True
    _ -> False

withAcceptedBundle :: (AcceptedResponseBundle -> Bool) -> Bool
withAcceptedBundle action = case phase0AcceptedResponseBundle of
  Left _ -> False
  Right bundle -> action bundle

withAcceptedLLVM
  :: (AcceptedResponseBundle -> LLVMArtifact -> Bool)
  -> Bool
withAcceptedLLVM action = withAcceptedBundle $ \bundle ->
  action bundle (lowerSystemsAcceptedResponse
    phase0AcceptedResponseLLVMTarget
    (acceptedResponseArtifact bundle))

mapAcceptedOp :: (SystemsOp -> SystemsOp) -> SystemsBlock -> SystemsBlock
mapAcceptedOp transform blockValue = blockValue
  { systemsBlockOps = map transform (systemsBlockOps blockValue) }

mapAcceptedLLVM :: (Text -> Text -> LLVMOp) -> LLVMBlock -> LLVMBlock
mapAcceptedLLVM transform blockValue = blockValue
  { llvmBlockOps = map mapOne (llvmBlockOps blockValue) }
  where
    mapOne operation = case operation of
      LLVMAcceptedResponse transport uploadId -> transform transport uploadId
      other -> other

mapSystemsFunction
  :: Text
  -> (SystemsFunction -> SystemsFunction)
  -> SystemsArtifact
  -> SystemsArtifact
mapSystemsFunction functionName transform artifact = artifact
  { systemsArtifactProgram = program
      { systemsProgramFunctions = Map.adjust
          transform
          functionName
          (systemsProgramFunctions program)
      }
  }
  where
    program = systemsArtifactProgram artifact

mapSystemsBlock
  :: Text
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
  -> SystemsArtifact
mapSystemsBlock functionName blockId transform =
  mapSystemsFunction functionName $ \function -> function
    { systemsFunctionBlocks = Map.adjust
        transform
        blockId
        (systemsFunctionBlocks function)
    }

mapLLVMBlock
  :: Text
  -> LLVMBlockId
  -> (LLVMBlock -> LLVMBlock)
  -> LLVMArtifact
  -> LLVMArtifact
mapLLVMBlock functionName blockId transform artifact = artifact
  { llvmArtifactModule = moduleValue
      { llvmFunctions = Map.adjust
          (\function -> function
            { llvmFunctionBlocks = Map.adjust
                transform
                blockId
                (llvmFunctionBlocks function)
            })
          functionName
          (llvmFunctions moduleValue)
      }
  }
  where
    moduleValue = llvmArtifactModule artifact

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
