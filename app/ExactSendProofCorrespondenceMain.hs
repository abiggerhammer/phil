{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types
import Phil.LLVM.ExactSend
import Phil.LLVM.ExactSendCertification
import Phil.LLVM.ExactSendProofCertification
import Phil.LLVM.IR
import Phil.Systems.ClientOutbound
import Phil.Systems.IR
import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--emit-llvm"] -> emitCurrentTarget
    _ -> runChecks

emitCurrentTarget :: IO ()
emitCurrentTarget = case phase0ClientOutboundBundle of
  Left err -> fail (show err)
  Right bundle -> TextIO.putStr $ llvmArtifactText $
    lowerSystemsExactSend phase0ExactSendLLVMTarget (clientOutboundArtifact bundle)

runChecks :: IO ()
runChecks = do
  results <- sequence
    [ test "current client-outbound Systems successor verifies" currentSystemsVerifies
    , test "current exact-send successor translation verifies" currentTranslationVerifies
    , test "historical translation-only CERT-013 remains valid only for predecessor source" historicalCertIsPredecessorScoped
    , test "current target maps exact payload owner once" exactPayloadMapping
    , test "current target preserves outbound Hello/Begin semantics as generic" outboundSemanticsRemainUnselected
    , test "source payload copy mutation is rejected" sourceCopyRejects
    , test "target payload-identity drift is rejected" targetPayloadDriftRejects
    , test "generic exact-send residue is rejected" genericExactSendRejects
    ]
  if and results then pure () else exitFailure

currentSystemsVerifies :: Bool
currentSystemsVerifies = withBundle $ \bundle ->
  verifyClientOutboundBundle bundle == Right ()

currentTranslationVerifies :: Bool
currentTranslationVerifies = withLLVM $ \bundle artifact ->
  verifyCurrentExactSendTranslation bundle artifact == Right ()

historicalCertIsPredecessorScoped :: Bool
historicalCertIsPredecessorScoped = withBundle $ \bundle ->
  case phase0ExactSendLLVMCertification of
    Left _ -> False
    Right historical ->
      let historicalSource = llvmContractSourceDigest
            (llvmArtifactContract (exactSendCertificationLLVM historical))
          currentSource = systemsArtifactDigest (clientOutboundArtifact bundle)
      in historicalSource /= currentSource

exactPayloadMapping :: Bool
exactPayloadMapping = withLLVM $ \bundle artifact ->
  let witness = clientOutboundWitness bundle
      moduleValue = llvmArtifactModule artifact
      transport = unValueId (clientOutboundTransport witness)
      payloadTarget = unValueId (clientOutboundPayload witness) <> ".owner"
  in case Map.lookup (clientOutboundFunction witness) (llvmFunctions moduleValue) of
      Nothing -> False
      Just client ->
        llvmFunctionParameters client ==
          [ LLVMParameter transport LLVMPointerParameter
          , LLVMParameter payloadTarget LLVMPointerParameter
          ]
          && case Map.lookup (LLVMBlockId "client.payload") (llvmFunctionBlocks client) of
              Nothing -> False
              Just blockValue -> length
                [ ()
                | LLVMExactSend site actualTransport actualPayload <- llvmBlockOps blockValue
                , runtimeSiteKind site == ExactSendBoundary
                , actualTransport == transport
                , actualPayload == payloadTarget
                ] == 1

outboundSemanticsRemainUnselected :: Bool
outboundSemanticsRemainUnselected = withLLVM $ \bundle artifact ->
  let witness = clientOutboundWitness bundle
      moduleValue = llvmArtifactModule artifact
  in doBool $ do
      client <- Map.lookup (clientOutboundFunction witness) (llvmFunctions moduleValue)
      entryBlock <- Map.lookup
        (LLVMBlockId (unBlockId (clientOutboundEntryBlock witness)))
        (llvmFunctionBlocks client)
      versionBlock <- Map.lookup
        (LLVMBlockId (unBlockId (clientOutboundVersionBlock witness)))
        (llvmFunctionBlocks client)
      pure
        ( llvmBlockOps entryBlock ==
            [ LLVMCall (clientOutboundSupportedVersionsCall witness)
            , LLVMCall (clientOutboundConstructHelloCall witness)
            , LLVMCall (clientOutboundSendHelloCall witness)
            ]
        && llvmBlockOps versionBlock ==
            [ LLVMPlain "borrowed view; no representation copy"
            , LLVMCall (clientOutboundDigestCall witness)
            , LLVMCall (clientOutboundProjectLengthCall witness)
            , LLVMCall (clientOutboundProjectKindCall witness)
            , LLVMCall (clientOutboundConstructBeginCall witness)
            , LLVMCall (clientOutboundSendBeginCall witness)
            ]
        )

sourceCopyRejects :: Bool
sourceCopyRejects = withBundle $ \bundle ->
  let witness = clientOutboundWitness bundle
      artifact = clientOutboundArtifact bundle
      program = systemsArtifactProgram artifact
      blockId = BlockId "client.payload"
      functions' = Map.adjust
        (\client -> client
          { systemsFunctionBlocks = Map.adjust
              (\blockValue -> blockValue
                { systemsBlockOps = systemsBlockOps blockValue <>
                    [ OpCopy
                        (clientOutboundPayload witness)
                        (ValueId "mutation.payload.copy")
                        (clientOutboundRecordDecision witness)
                    ]
                })
              blockId
              (systemsFunctionBlocks client)
          })
        (clientOutboundFunction witness)
        (systemsProgramFunctions program)
      mutatedProgram = program { systemsProgramFunctions = functions' }
      targetDigest = systemsProgramDigest mutatedProgram
      decisions = Map.map (rebindDecision targetDigest)
        (loweringLedgerDecisions (systemsArtifactLoweringLedger artifact))
      mutatedArtifact = SystemsArtifact
        mutatedProgram
        ((systemsArtifactStageContract artifact) { stageTargetArtifactDigest = targetDigest })
        (LoweringLedger decisions (deriveLoweringLedgerRoot decisions))
      mutatedBundle = bundle { clientOutboundArtifact = mutatedArtifact }
      llvmArtifact = lowerSystemsExactSend phase0ExactSendLLVMTarget mutatedArtifact
  in isLeft (verifyCurrentExactSendTranslation mutatedBundle llvmArtifact)

rebindDecision :: Digest -> LoweringDecision -> LoweringDecision
rebindDecision targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

targetPayloadDriftRejects :: Bool
targetPayloadDriftRejects = withLLVM $ \bundle artifact ->
  let witness = clientOutboundWitness bundle
      functionName = clientOutboundFunction witness
      blockId = LLVMBlockId "client.payload"
      moduleValue = llvmArtifactModule artifact
      functions' = Map.adjust
        (\client -> client
          { llvmFunctionBlocks = Map.adjust
              (\blockValue -> blockValue
                { llvmBlockOps = map mutate (llvmBlockOps blockValue) })
              blockId
              (llvmFunctionBlocks client)
          })
        functionName
        (llvmFunctions moduleValue)
      mutate operation = case operation of
        LLVMExactSend site transport _ -> LLVMExactSend site transport "mutation.other.owner"
        other -> other
      mutatedModule = moduleValue { llvmFunctions = functions' }
      mutated = artifact
        { llvmArtifactModule = mutatedModule
        , llvmArtifactText = renderLLVMModule mutatedModule
        }
  in isLeft (verifyCurrentExactSendTranslation bundle mutated)

genericExactSendRejects :: Bool
genericExactSendRejects = withLLVM $ \bundle artifact ->
  let witness = clientOutboundWitness bundle
      functionName = clientOutboundFunction witness
      blockId = LLVMBlockId "client.payload"
      moduleValue = llvmArtifactModule artifact
      functions' = Map.adjust
        (\client -> client
          { llvmFunctionBlocks = Map.adjust
              (\blockValue -> blockValue
                { llvmBlockOps = map mutate (llvmBlockOps blockValue) })
              blockId
              (llvmFunctionBlocks client)
          })
        functionName
        (llvmFunctions moduleValue)
      mutate operation = case operation of
        LLVMExactSend site _ _ -> LLVMRuntime site "send_exact"
        other -> other
      mutatedModule = moduleValue { llvmFunctions = functions' }
      mutated = artifact
        { llvmArtifactModule = mutatedModule
        , llvmArtifactText = renderLLVMModule mutatedModule
        }
  in isLeft (verifyCurrentExactSendTranslation bundle mutated)

withBundle :: (ClientOutboundBundle -> Bool) -> Bool
withBundle action = case phase0ClientOutboundBundle of
  Left _ -> False
  Right bundle -> action bundle

withLLVM :: (ClientOutboundBundle -> LLVMArtifact -> Bool) -> Bool
withLLVM action = case phase0ClientOutboundBundle of
  Left _ -> False
  Right bundle -> action bundle $
    lowerSystemsExactSend phase0ExactSendLLVMTarget (clientOutboundArtifact bundle)

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
