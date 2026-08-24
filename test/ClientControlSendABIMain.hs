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
    [ test "client control-send translation verifies" candidateVerifies
    , test "Hello and refinement share exact version-set identity" sharedVersionSet
    , test "Begin send consumes exact derived operands" exactBeginOperands
    , test "semantic record handles and payload view erase after fusion" fusedRecordResidueAbsent
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies =
  verifyPhase0ClientControlSendLLVM == Right ()

sharedVersionSet :: Bool
sharedVersionSet = withCandidate $ \bundle artifact ->
  let outbound = clientOutboundWitness bundle
      versionChoice = phase0VersionSessionChoiceWitness
      moduleValue = llvmArtifactModule artifact
      versions = unValueId (clientOutboundSupportedVersions outbound)
      transport = unValueId (clientOutboundTransport outbound)
      selected = unValueId (versionChoiceClientSelectedVersion versionChoice)
  in doBool $ do
      client <- Map.lookup "UploadClient" (llvmFunctions moduleValue)
      entry <- Map.lookup
        (LLVMBlockId (unBlockId (clientOutboundEntryBlock outbound)))
        (llvmFunctionBlocks client)
      refinement <- Map.lookup
        (LLVMBlockId (unBlockId (versionChoiceClientVersionTarget versionChoice)))
        (llvmFunctionBlocks client)
      pure $
        LLVMClientSendHello transport versions `elem` llvmBlockOps entry
          && case llvmBlockTerminator refinement of
              LLVMVersionRefinementWithSet _ t offered s _ _ ->
                t == transport && offered == versions && s == selected
              _ -> False

exactBeginOperands :: Bool
exactBeginOperands = withCandidate $ \bundle artifact ->
  let outbound = clientOutboundWitness bundle
      moduleValue = llvmArtifactModule artifact
      transport = unValueId (clientOutboundTransport outbound)
      payloadLength = unValueId (clientOutboundPayloadLength outbound)
      payloadKind = unValueId (clientOutboundPayloadKind outbound)
      digest = unValueId (clientOutboundDeclaredDigest outbound)
  in doBool $ do
      client <- Map.lookup "UploadClient" (llvmFunctions moduleValue)
      versionBlock <- Map.lookup
        (LLVMBlockId (unBlockId (clientOutboundVersionBlock outbound)))
        (llvmFunctionBlocks client)
      pure $ LLVMClientSendBegin transport payloadLength payloadKind digest
        `elem` llvmBlockOps versionBlock

fusedRecordResidueAbsent :: Bool
fusedRecordResidueAbsent = withCandidate $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (not . (`Text.isInfixOf` rendered))
      [ "%client_hello ="
      , "%client_begin ="
      , "%client_payload_view ="
      , "@phil_call_construct_Hello"
      , "@phil_call_construct_Begin"
      ]

withCandidate :: (ClientOutboundBundle -> LLVMArtifact -> Bool) -> Bool
withCandidate action = case phase0ClientOutboundBundle of
  Left _ -> False
  Right bundle ->
    let artifact = lowerSystemsClientControlSend
          phase0ClientControlSendLLVMTarget
          (clientOutboundArtifact bundle)
    in action bundle artifact

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
