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
    [ test "payload/cancel translation verifies" translationPasses
    , test "PHIL-LLVM-CERT-009 closes" certificationPasses
    , test "payload select lowers to exact transport and 0x01" exactPayloadSelect
    , test "cancel select lowers to exact transport and 0x00" exactCancelSelect
    , test "server offer lowers to exact validated receiver dispatch" exactServerOffer
    , test "legacy generic payload/cancel calls are absent" noLegacyCalls
    , test "unlowered session-select poison is absent" noChoicePoison
    , test "wrong payload selector code is rejected" wrongPayloadCodeRejects
    , test "wrong server continuation mapping is rejected" wrongServerTargetRejects
    ]
  if and results then pure () else exitFailure

translationPasses :: Bool
translationPasses = case phase0PayloadCancelChoiceBundle of
  Left _ -> False
  Right bundle -> case verifyPayloadCancelChoiceTranslation bundle (artifactFor bundle) of
    Right () -> True
    Left _ -> False

certificationPasses :: Bool
certificationPasses = case verifyPhase0PayloadCancelChoiceLLVMCertification of
  Right () -> True
  Left _ -> False

exactPayloadSelect :: Bool
exactPayloadSelect = withBundle $ \bundle artifact ->
  let witness = payloadCancelChoiceWitness bundle
  in selectAt artifact
      (payloadCancelClientFunction witness)
      (payloadCancelClientPayloadSelectBlock witness)
      (unValueId (payloadCancelClientTransport witness))
      payloadChoiceCode

exactCancelSelect :: Bool
exactCancelSelect = withBundle $ \bundle artifact ->
  let witness = payloadCancelChoiceWitness bundle
  in selectAt artifact
      (payloadCancelClientFunction witness)
      (payloadCancelClientCancelSelectBlock witness)
      (unValueId (payloadCancelClientTransport witness))
      cancelChoiceCode

exactServerOffer :: Bool
exactServerOffer = withBundle $ \bundle artifact ->
  let witness = payloadCancelChoiceWitness bundle
      expected = LLVMPayloadCancelOffer
        (unValueId (payloadCancelServerTransport witness))
        (LLVMBlockId (unBlockId (payloadCancelPayloadTarget witness)))
        (LLVMBlockId (unBlockId (payloadCancelCancelTarget witness)))
  in case lookupBlock artifact
      (payloadCancelServerFunction witness)
      (payloadCancelServerOfferBlock witness) of
      Just blockValue -> llvmBlockTerminator blockValue == expected
      Nothing -> False

noLegacyCalls :: Bool
noLegacyCalls = withBundle $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in not (Text.isInfixOf "phil_call_select_payload" rendered)
      && not (Text.isInfixOf "phil_call_select_cancel" rendered)
      && not (Text.isInfixOf "phil_call_receive_payload_cancel_label" rendered)

noChoicePoison :: Bool
noChoicePoison = withBundle $ \_ artifact ->
  not (Text.isInfixOf "unlowered-session-select" (llvmArtifactText artifact))

wrongPayloadCodeRejects :: Bool
wrongPayloadCodeRejects = withBundle $ \bundle artifact ->
  let witness = payloadCancelChoiceWitness bundle
      mutated = mapBlock artifact
        (payloadCancelClientFunction witness)
        (payloadCancelClientPayloadSelectBlock witness) $ \blockValue ->
          blockValue { llvmBlockOps = case llvmBlockOps blockValue of
            LLVMPayloadCancelSelect transport _ : rest ->
              LLVMPayloadCancelSelect transport 7 : rest
            operations -> operations
          }
  in case verifyPayloadCancelChoiceLLVMWitness bundle mutated of
      Left PayloadCancelChoiceClientSelectMismatch {} -> True
      _ -> False

wrongServerTargetRejects :: Bool
wrongServerTargetRejects = withBundle $ \bundle artifact ->
  let witness = payloadCancelChoiceWitness bundle
      mutated = mapBlock artifact
        (payloadCancelServerFunction witness)
        (payloadCancelServerOfferBlock witness) $ \blockValue ->
          blockValue { llvmBlockTerminator = case llvmBlockTerminator blockValue of
            LLVMPayloadCancelOffer transport _ cancelTarget ->
              LLVMPayloadCancelOffer transport cancelTarget cancelTarget
            other -> other
          }
  in case verifyPayloadCancelChoiceLLVMWitness bundle mutated of
      Left PayloadCancelChoiceServerOfferMismatch {} -> True
      _ -> False

selectAt :: LLVMArtifact -> Text.Text -> BlockId -> Text.Text -> Int -> Bool
selectAt artifact functionName blockId transport code =
  case lookupBlock artifact functionName blockId of
    Just blockValue -> case llvmBlockOps blockValue of
      LLVMPayloadCancelSelect actualTransport actualCode : _ ->
        actualTransport == transport && actualCode == code
      _ -> False
    Nothing -> False

withBundle :: (PayloadCancelChoiceBundle -> LLVMArtifact -> Bool) -> Bool
withBundle action = case phase0PayloadCancelChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle (artifactFor bundle)

artifactFor :: PayloadCancelChoiceBundle -> LLVMArtifact
artifactFor bundle = lowerSystemsPayloadCancelChoice
  phase0PayloadCancelChoiceLLVMTarget
  (payloadCancelChoiceArtifact bundle)

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
          { llvmFunctionBlocks = Map.adjust
              transform
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
