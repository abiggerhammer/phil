{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "final-response receive translation verifies" translationPasses
    , test "offer lowers to exact decoder operands and targets" exactOffer
    , test "accepted payload binds then reaches record_upload_id" exactAcceptedPayloadUse
    , test "rejected DigestFailure has no target representation" rejectedReasonErased
    , test "legacy generic final-response calls are absent" noLegacyCalls
    , test "wrong accepted target is rejected" wrongAcceptedTargetRejects
    , test "missing accepted payload binding is rejected" missingBindingRejects
    ]
  if and results then pure () else exitFailure

translationPasses :: Bool
translationPasses = case phase0SessionChoiceBundle of
  Left _ -> False
  Right bundle -> case verifyFinalResponseReceiveTranslation bundle (artifactFor bundle) of
    Right () -> True
    Left _ -> False

exactOffer :: Bool
exactOffer = withBundle $ \bundle artifact ->
  let witness = sessionChoiceWitness bundle
      expected = LLVMFinalResponseOffer
        (unValueId (sessionChoiceTransport witness))
        (unValueId (sessionChoiceAcceptedPayload witness))
        (LLVMBlockId (unBlockId (sessionChoiceAcceptedTarget witness)))
        (LLVMBlockId (unBlockId (sessionChoiceRejectedTarget witness)))
  in case lookupBlock artifact (sessionChoiceFunction witness) (sessionChoiceOfferBlock witness) of
      Just blockValue -> llvmBlockTerminator blockValue == expected
      Nothing -> False

exactAcceptedPayloadUse :: Bool
exactAcceptedPayloadUse = withBundle $ \bundle artifact ->
  let witness = sessionChoiceWitness bundle
      uploadId = unValueId (sessionChoiceAcceptedPayload witness)
  in case lookupBlock artifact (sessionChoiceFunction witness) (sessionChoiceAcceptedTarget witness) of
      Just blockValue -> llvmBlockOps blockValue
        == [LLVMFinalResponsePayloadBinding uploadId, LLVMRecordUploadId uploadId]
      Nothing -> False

rejectedReasonErased :: Bool
rejectedReasonErased = withBundle $ \_ artifact ->
  not (Text.isInfixOf "client_digest_failure" (llvmArtifactText artifact))

noLegacyCalls :: Bool
noLegacyCalls = withBundle $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in not (Text.isInfixOf "phil_call_receive_accepted_rejected_label" rendered)
      && not (Text.isInfixOf "phil_call_record_upload_id" rendered)

wrongAcceptedTargetRejects :: Bool
wrongAcceptedTargetRejects = withBundle $ \bundle artifact ->
  let witness = sessionChoiceWitness bundle
      mutated = mapBlock artifact (sessionChoiceFunction witness) (sessionChoiceOfferBlock witness) $ \blockValue ->
        blockValue { llvmBlockTerminator = case llvmBlockTerminator blockValue of
LLVMFinalResponseOffer transport uploadId _ rejected ->
  LLVMFinalResponseOffer transport uploadId rejected rejected
other -> other
        }
  in case verifyFinalResponseReceiveWitness bundle mutated of
      Left FinalResponseReceiveOfferMismatch {} -> True
      _ -> False

missingBindingRejects :: Bool
missingBindingRejects = withBundle $ \bundle artifact ->
  let witness = sessionChoiceWitness bundle
      mutated = mapBlock artifact (sessionChoiceFunction witness) (sessionChoiceAcceptedTarget witness) $ \blockValue ->
        blockValue { llvmBlockOps = [LLVMRecordUploadId (unValueId (sessionChoiceAcceptedPayload witness))] }
  in case verifyFinalResponseReceiveWitness bundle mutated of
      Left FinalResponseReceiveAcceptedOpsMismatch {} -> True
      _ -> False

withBundle :: (SessionChoiceBundle -> LLVMArtifact -> Bool) -> Bool
withBundle action = case phase0SessionChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle (artifactFor bundle)

artifactFor :: SessionChoiceBundle -> LLVMArtifact
artifactFor bundle = lowerSystemsFinalResponseReceive
  phase0FinalResponseReceiveLLVMTarget
  (sessionChoiceArtifact bundle)

lookupBlock :: LLVMArtifact -> Text.Text -> BlockId -> Maybe LLVMBlock
lookupBlock artifact functionName blockId = do
  function <- Map.lookup functionName (llvmFunctions (llvmArtifactModule artifact))
  Map.lookup (LLVMBlockId (unBlockId blockId)) (llvmFunctionBlocks function)

mapBlock
  :: LLVMArtifact
  -> Text.Text
  -> BlockId
  -> (LLVMBlock -> LLVMBlock)
  -> LLVMArtifact
mapBlock artifact functionName blockId transform =
  let moduleValue = llvmArtifactModule artifact
      functions = llvmFunctions moduleValue
      functions' = Map.adjust
        (\function -> function
{ llvmFunctionBlocks = Map.adjust transform
    (LLVMBlockId (unBlockId blockId))
    (llvmFunctionBlocks function)
})
        functionName
        functions
      moduleValue' = moduleValue { llvmFunctions = functions' }
  in artifact
      { llvmArtifactModule = moduleValue'
      , llvmArtifactText = renderLLVMModule moduleValue'
      }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
