{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.LLVM.ClientControlSend
import Phil.LLVM.IR
import Phil.Systems.ClientOutbound
import Phil.Systems.IR
import Phil.Systems.VersionSessionChoice
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "client-control-send translation verifies" currentCandidateVerifies
    , test "Hello/refinement share exact offered-version identity" sharedVersionSet
    , test "Begin operands derive from exact payload owner" exactBeginDerivations
    , test "record/view fusion leaves no target residue" fusionResidueAbsent
    , test "exact payload send remains physically preserved" exactSendPreserved
    , test "wrong refinement version-set identity is rejected" wrongRefinementSetRejects
    , test "Begin digest identity drift is rejected" beginDigestDriftRejects
    , test "ambient offered-version state is rejected" ambientStateRejects
    , test "generic outbound residue is rejected" genericResidueRejects
    ]
  if and results then pure () else exitFailure

currentCandidateVerifies :: Bool
currentCandidateVerifies = verifyPhase0ClientControlSendLLVM == Right ()

sharedVersionSet :: Bool
sharedVersionSet = withCandidate $ \bundle artifact ->
  let outbound = clientOutboundWitness bundle
      versionChoice = phase0VersionSessionChoiceWitness
      versions = unValueId (clientOutboundSupportedVersions outbound)
      transport = unValueId (clientOutboundTransport outbound)
      selected = unValueId (versionChoiceClientSelectedVersion versionChoice)
      moduleValue = llvmArtifactModule artifact
  in doBool $ do
      client <- Map.lookup "UploadClient" (llvmFunctions moduleValue)
      entry <- Map.lookup
        (LLVMBlockId (unBlockId (clientOutboundEntryBlock outbound)))
        (llvmFunctionBlocks client)
      refinement <- Map.lookup
        (LLVMBlockId (unBlockId (versionChoiceClientVersionTarget versionChoice)))
        (llvmFunctionBlocks client)
      pure $
        llvmBlockOps entry ==
          [ LLVMClientSupportedVersions versions
          , LLVMClientSendHello transport versions
          ]
        && case llvmBlockTerminator refinement of
          LLVMVersionRefinementWithSet _ t v s yes no ->
            t == transport
              && v == versions
              && s == selected
              && yes == LLVMBlockId (unBlockId (versionChoiceClientVersionSuccess versionChoice))
              && no == LLVMBlockId (unBlockId (versionChoiceClientVersionFailure versionChoice))
          _ -> False

exactBeginDerivations :: Bool
exactBeginDerivations = withCandidate $ \bundle artifact ->
  let outbound = clientOutboundWitness bundle
      transport = unValueId (clientOutboundTransport outbound)
      payloadOwner = unValueId (clientOutboundPayload outbound) <> ".owner"
      digest = unValueId (clientOutboundDeclaredDigest outbound)
      payloadLength = unValueId (clientOutboundPayloadLength outbound)
      payloadKind = unValueId (clientOutboundPayloadKind outbound)
      moduleValue = llvmArtifactModule artifact
  in doBool $ do
      client <- Map.lookup "UploadClient" (llvmFunctions moduleValue)
      versionBlock <- Map.lookup
        (LLVMBlockId (unBlockId (clientOutboundVersionBlock outbound)))
        (llvmFunctionBlocks client)
      pure (llvmBlockOps versionBlock ==
        [ LLVMClientSHA256 digest payloadOwner
        , LLVMClientPayloadLength payloadLength payloadOwner
        , LLVMClientPayloadKind payloadKind payloadOwner
        , LLVMClientSendBegin transport payloadLength payloadKind digest
        ])

fusionResidueAbsent :: Bool
fusionResidueAbsent = withCandidate $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (not . (`Text.isInfixOf` rendered))
      [ "%client_hello ="
      , "%client_begin ="
      , "%client_payload_view ="
      , "@phil_call_construct_Hello"
      , "@phil_call_construct_Begin"
      ]

exactSendPreserved :: Bool
exactSendPreserved = withCandidate $ \bundle artifact ->
  let outbound = clientOutboundWitness bundle
      transport = unValueId (clientOutboundTransport outbound)
      payloadOwner = unValueId (clientOutboundPayload outbound) <> ".owner"
      moduleValue = llvmArtifactModule artifact
  in doBool $ do
      client <- Map.lookup "UploadClient" (llvmFunctions moduleValue)
      payloadBlock <- Map.lookup (LLVMBlockId "client.payload") (llvmFunctionBlocks client)
      pure $ case
        [ ()
        | LLVMExactSend _ t p <- llvmBlockOps payloadBlock
        , t == transport
        , p == payloadOwner
        ] of
          [_] -> True
          _ -> False

wrongRefinementSetRejects :: Bool
wrongRefinementSetRejects = withCandidate $ \bundle artifact ->
  let witness = phase0VersionSessionChoiceWitness
      blockId = LLVMBlockId (unBlockId (versionChoiceClientVersionTarget witness))
      mutated = mutateClientBlock blockId mutateTerm artifact
      mutateTerm blockValue = blockValue
        { llvmBlockTerminator = case llvmBlockTerminator blockValue of
            LLVMVersionRefinementWithSet site transport _versions selected yes no ->
              LLVMVersionRefinementWithSet site transport "wrong.offered.versions" selected yes no
            other -> other
        }
  in isLeft (verifyClientControlSendLLVMWitness bundle mutated)

beginDigestDriftRejects :: Bool
beginDigestDriftRejects = withCandidate $ \bundle artifact ->
  let outbound = clientOutboundWitness bundle
      blockId = LLVMBlockId (unBlockId (clientOutboundVersionBlock outbound))
      mutateOp operation = case operation of
        LLVMClientSendBegin transport payloadLength payloadKind _digest ->
          LLVMClientSendBegin transport payloadLength payloadKind "wrong.digest"
        other -> other
      mutated = mutateClientBlock blockId
        (\blockValue -> blockValue { llvmBlockOps = map mutateOp (llvmBlockOps blockValue) })
        artifact
  in isLeft (verifyClientControlSendLLVMWitness bundle mutated)

ambientStateRejects :: Bool
ambientStateRejects = withCandidate $ \bundle artifact ->
  let mutated = artifact
        { llvmArtifactText = llvmArtifactText artifact <> "\ncurrent_offered_versions\n" }
  in isLeft (verifyClientControlSendLLVMWitness bundle mutated)

genericResidueRejects :: Bool
genericResidueRejects = withCandidate $ \bundle artifact ->
  let mutated = artifact
        { llvmArtifactText = llvmArtifactText artifact <> "\n@phil_call_send_Hello\n" }
  in isLeft (verifyClientControlSendLLVMWitness bundle mutated)

mutateClientBlock
  :: LLVMBlockId
  -> (LLVMBlock -> LLVMBlock)
  -> LLVMArtifact
  -> LLVMArtifact
mutateClientBlock blockId transform artifact =
  let moduleValue = llvmArtifactModule artifact
      functions' = Map.adjust
        (\function -> function
          { llvmFunctionBlocks = Map.adjust transform blockId (llvmFunctionBlocks function) })
        "UploadClient"
        (llvmFunctions moduleValue)
  in artifact { llvmArtifactModule = moduleValue { llvmFunctions = functions' } }

withCandidate :: (ClientOutboundBundle -> LLVMArtifact -> Bool) -> Bool
withCandidate action = case phase0ClientOutboundBundle of
  Left _ -> False
  Right bundle ->
    let artifact = lowerSystemsClientControlSend
          phase0ClientControlSendLLVMTarget
          (clientOutboundArtifact bundle)
    in action bundle artifact

isLeft :: Either a b -> Bool
isLeft value = case value of
  Left _ -> True
  Right _ -> False

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
