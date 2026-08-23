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
    [ test "rejected-response Systems witness verifies" systemsCandidatePasses
    , test "rejected-response LLVM candidate verifies" llvmCandidatePasses
    , test "rejected-response certification closes" certificationPasses
    , test "rejected-response ABI binds exact two-octet wire payload" wireDescriptorBound
    , test "rejected-response ABI keeps diagnostics out of protocol" diagnosticsDescriptorBound
    , test "rejected-response ABI keeps outer framing separate" framingDescriptorBound
    , test "wrong Systems rejected transport is rejected" wrongSystemsTransportRejects
    , test "missing Systems payload release is rejected" missingSystemsReleaseRejects
    , test "wrong digest predecessor is rejected" wrongDigestPredecessorRejects
    , test "wrong LLVM rejected transport is rejected" wrongLLVMTransportRejects
    , test "wrong LLVM rejected reason code is rejected" wrongLLVMReasonRejects
    , test "generic nullary rejected call is rejected" genericRejectedCallRejects
    , test "ambient last-digest-error state is rejected" ambientDigestStateRejects
    , test "accepted response stays explicit in successor profile" acceptedResponsePreserved
    ]
  if and results then pure () else exitFailure

systemsCandidatePasses :: Bool
systemsCandidatePasses = case phase0RejectedResponseBundle of
  Right _ -> True
  Left _ -> False

llvmCandidatePasses :: Bool
llvmCandidatePasses = verifyPhase0RejectedResponseLLVM == Right ()

certificationPasses :: Bool
certificationPasses = verifyPhase0RejectedResponseLLVMCertification == Right ()

wireDescriptorBound :: Bool
wireDescriptorBound = all (`Text.isInfixOf` rejectedResponseABIDescriptor)
  [ "rejected-wire-length=2-octets"
  , "rejected-wire-tag=0x00"
  , "rejected-reason-width=1-octet"
  , "rejected-reason-0x01=DigestMismatch"
  , "rejected-reason-other-codes=reserved-v1"
  ]

diagnosticsDescriptorBound :: Bool
diagnosticsDescriptorBound = all (`Text.isInfixOf` rejectedResponseABIDescriptor)
  [ "digest-failure-protocol-observable-class=singleton-DigestMismatch"
  , "digest-diagnostic-detail=not-protocol-data"
  , "digest-mismatch-reason-lowering=control-flow-singleton-to-i8-0x01"
  ]

framingDescriptorBound :: Bool
framingDescriptorBound =
  Text.isInfixOf
    "rejected-outer-framing=not-defined-by-this-profile"
    rejectedResponseABIDescriptor

wrongSystemsTransportRejects :: Bool
wrongSystemsTransportRejects = withRejectedBundle $ \bundle ->
  let witness = rejectedResponseWitness bundle
      badArtifact = mapSystemsBlock
        (rejectedResponseFunction witness)
        (rejectedResponseBlock witness)
        (mapRejectedOp $ \operation -> operation
          { runtimeCallInputs = [ValueId "server.frame.begin"] })
        (rejectedResponseArtifact bundle)
  in case verifyRejectedResponseWitness badArtifact witness of
    Left RejectedResponseOperationMismatch {} -> True
    _ -> False

missingSystemsReleaseRejects :: Bool
missingSystemsReleaseRejects = withRejectedBundle $ \bundle ->
  let witness = rejectedResponseWitness bundle
      badArtifact = mapSystemsBlock
        (rejectedResponseFunction witness)
        (rejectedResponseBlock witness)
        (\blockValue -> blockValue
          { systemsBlockOps = drop 1 (systemsBlockOps blockValue) })
        (rejectedResponseArtifact bundle)
  in case verifyRejectedResponseWitness badArtifact witness of
    Left RejectedResponseOperationMismatch {} -> True
    _ -> False

wrongDigestPredecessorRejects :: Bool
wrongDigestPredecessorRejects = withRejectedBundle $ \bundle ->
  let witness = rejectedResponseWitness bundle
      badArtifact = mapSystemsBlock
        (rejectedResponseFunction witness)
        (rejectedResponseDigestBlock witness)
        (\blockValue -> blockValue
          { systemsBlockTerminator = case systemsBlockTerminator blockValue of
              term@TermRuntimeCheck {} -> term { checkFailure = BlockId "server.early_eof" }
              other -> other
          })
        (rejectedResponseArtifact bundle)
  in case verifyRejectedResponseWitness badArtifact witness of
    Left RejectedResponseDigestPredecessorMismatch {} -> True
    _ -> False

wrongLLVMTransportRejects :: Bool
wrongLLVMTransportRejects = withRejectedLLVM $ \bundle artifact ->
  let witness = rejectedResponseWitness bundle
      badArtifact = mapLLVMBlock
        (rejectedResponseFunction witness)
        (LLVMBlockId (unBlockId (rejectedResponseBlock witness)))
        (mapRejectedLLVM $ \_ reason -> LLVMRejectedResponse "server.wrong_transport" reason)
        artifact
  in case verifyRejectedResponseTranslation bundle badArtifact of
    Left RejectedResponseLLVMOperationMismatch {} -> True
    _ -> False

wrongLLVMReasonRejects :: Bool
wrongLLVMReasonRejects = withRejectedLLVM $ \bundle artifact ->
  let witness = rejectedResponseWitness bundle
      badArtifact = mapLLVMBlock
        (rejectedResponseFunction witness)
        (LLVMBlockId (unBlockId (rejectedResponseBlock witness)))
        (mapRejectedLLVM $ \transport _ -> LLVMRejectedResponse transport 2)
        artifact
  in case verifyRejectedResponseTranslation bundle badArtifact of
    Left RejectedResponseLLVMOperationMismatch {} -> True
    _ -> False

genericRejectedCallRejects :: Bool
genericRejectedCallRejects = withRejectedLLVM $ \bundle artifact ->
  let badArtifact = artifact
        { llvmArtifactText = llvmArtifactText artifact
            <> "\ndeclare void @phil_call_select_rejected()\n" }
  in case verifyRejectedResponseTranslation bundle badArtifact of
    Left RejectedResponseGenericCallDetected {} -> True
    _ -> False

ambientDigestStateRejects :: Bool
ambientDigestStateRejects = withRejectedLLVM $ \bundle artifact ->
  let badArtifact = artifact
        { llvmArtifactText = llvmArtifactText artifact
            <> "\n@phil_last_digest_error = external global i8\n" }
  in case verifyRejectedResponseTranslation bundle badArtifact of
    Left RejectedResponseAmbientStateDetected {} -> True
    _ -> False

acceptedResponsePreserved :: Bool
acceptedResponsePreserved = withRejectedLLVM $ \_ artifact ->
  Text.isInfixOf "@phil_runtime_select_accepted(ptr %server_transport, ptr %server_upload_id)"
    (llvmArtifactText artifact)

withRejectedBundle :: (RejectedResponseBundle -> Bool) -> Bool
withRejectedBundle action = case phase0RejectedResponseBundle of
  Left _ -> False
  Right bundle -> action bundle

withRejectedLLVM
  :: (RejectedResponseBundle -> LLVMArtifact -> Bool)
  -> Bool
withRejectedLLVM action = withRejectedBundle $ \bundle ->
  action bundle (lowerSystemsRejectedResponse
    phase0RejectedResponseLLVMTarget
    (rejectedResponseArtifact bundle))

mapRejectedOp :: (SystemsOp -> SystemsOp) -> SystemsBlock -> SystemsBlock
mapRejectedOp transform blockValue = blockValue
  { systemsBlockOps = map mapOne (systemsBlockOps blockValue) }
  where
    mapOne operation@OpRuntimeCall { runtimeCallName = "select rejected" } = transform operation
    mapOne other = other

mapRejectedLLVM :: (Text -> Int -> LLVMOp) -> LLVMBlock -> LLVMBlock
mapRejectedLLVM transform blockValue = blockValue
  { llvmBlockOps = map mapOne (llvmBlockOps blockValue) }
  where
    mapOne operation = case operation of
      LLVMRejectedResponse transport reason -> transform transport reason
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
