{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "recognized-record Systems candidate verifies" systemsCandidatePasses
    , test "Begin.length consumes the exact recognized Begin record" projectionConsumesExactRecord
    , test "recognized-record ABI v1 LLVM candidate verifies" llvmCandidatePasses
    , test "ABI v1 materializes opaque recognition handle and typed accessor" abiShapeIsConcrete
    , test "runtime linker symbols do not encode assurance evidence identity" runtimeSymbolsExcludeEvidence
    , test "ABI v1 emits no direct record layout or pointer strengthening" noPrematureRecordLayout
    , test "wrong projected record input is rejected" wrongProjectionInputRejects
    , test "exact-receive dependency drift is rejected by translation validation" receiveDependencyDriftRejects
    ]
  if and results then pure () else exitFailure

systemsCandidatePasses :: Bool
systemsCandidatePasses = case phase0RecognizedRecordBundle of
  Left _ -> False
  Right bundle -> verifyRecognizedRecordBundle bundle == Right ()

projectionConsumesExactRecord :: Bool
projectionConsumesExactRecord = case phase0RecognizedRecordBundle of
  Left _ -> False
  Right bundle ->
    case lookupSystemsBlock "UploadServer" "server.begin.commit" (recognizedRecordArtifact bundle) of
      Nothing -> False
      Just blockValue -> any isExpectedProjection (systemsBlockOps blockValue)
  where
    isExpectedProjection operation = case operation of
      OpRuntimeCall
        { runtimeCallName = "project recognized Begin.length"
        , runtimeCallInputs = [ValueId "server.begin_record"]
        , runtimeCallOutputs = [ValueId "server.begin_length"]
        , runtimeCallSite = Nothing
        } -> True
      _ -> False

llvmCandidatePasses :: Bool
llvmCandidatePasses = verifyPhase0RecognizedRecordLLVM == Right ()

abiShapeIsConcrete :: Bool
abiShapeIsConcrete = case phase0RecognizedRecordLLVMArtifact of
  Left _ -> False
  Right artifact ->
    let rendered = llvmArtifactText artifact
    in and
      [ Text.isInfixOf "declare { i8, ptr } @phil_runtime_recognize_Begin()" rendered
      , Text.isInfixOf "icmp eq i8 %phil_recognition_status_server_version, 1" rendered
      , Text.isInfixOf "%server_begin_record = extractvalue { i8, ptr } %phil_recognition_result_server_version, 1" rendered
      , Text.isInfixOf "declare i64 @phil_record_Begin_get_length(ptr)" rendered
      , Text.isInfixOf "%server_begin_length = call i64 @phil_record_Begin_get_length(ptr %server_begin_record)" rendered
      , Text.isInfixOf "declare i1 @phil_runtime_receive_exact_u64(i64)" rendered
      , Text.isInfixOf "call i1 @phil_runtime_receive_exact_u64(i64 %server_begin_length)" rendered
      ]

runtimeSymbolsExcludeEvidence :: Bool
runtimeSymbolsExcludeEvidence = case (phase0RecognizedRecordBundle, phase0RecognizedRecordLLVMArtifact) of
  (Right bundle, Right artifact) ->
    let rendered = llvmArtifactText artifact
        evidenceNames =
          [ unEvidenceEntryId (runtimeSiteEvidence site)
          | site <- runtimeSites (recognizedRecordArtifact bundle)
          ]
    in all (not . (`Text.isInfixOf` rendered)) evidenceNames
        && Text.isInfixOf "@phil_runtime_recognize_Begin" rendered
        && Text.isInfixOf "@phil_runtime_receive_exact_u64" rendered
  _ -> False

noPrematureRecordLayout :: Bool
noPrematureRecordLayout = case phase0RecognizedRecordLLVMArtifact of
  Left _ -> False
  Right artifact ->
    let rendered = llvmArtifactText artifact
    in all (`Text.isInfixOf` rendered) []
        && not (Text.isInfixOf "getelementptr" rendered)
        && not (Text.isInfixOf " inbounds " rendered)
        && not (Text.isInfixOf " nonnull" rendered)
        && not (Text.isInfixOf " dereferenceable" rendered)
        && not (Text.isInfixOf " load " rendered)

wrongProjectionInputRejects :: Bool
wrongProjectionInputRejects = case phase0RecognizedRecordBundle of
  Left _ -> False
  Right bundle ->
    let artifact = recognizedRecordArtifact bundle
        badArtifact = adjustSystemsBlock "UploadServer" "server.begin.commit"
          (\blockValue -> blockValue
            { systemsBlockOps = map removeRecordInput (systemsBlockOps blockValue) })
          artifact
    in case verifyRecognizedRecordWitnesses badArtifact (recognizedRecordWitnesses bundle) of
        Left RecognizedRecordProjectionInputMismatch {} -> True
        _ -> False
  where
    removeRecordInput operation = case operation of
      call@OpRuntimeCall { runtimeCallName = "project recognized Begin.length" } ->
        call { runtimeCallInputs = [] }
      _ -> operation

receiveDependencyDriftRejects :: Bool
receiveDependencyDriftRejects = case
    (phase0RecognizedRecordBundle, phase0RecognizedRecordLLVMArtifact,
      phase0RecognizedRecordLLVMVerificationContext) of
  (Right bundle, Right artifact, Right context) ->
    let bad = rebindLLVMArtifact $
          adjustLLVMBlock "UploadServer" "server.payload"
            (\blockValue -> case llvmBlockTerminator blockValue of
              LLVMRuntimeBranch site _ yes no -> blockValue
                { llvmBlockTerminator = LLVMRuntimeBranch
                    site "abi-v1:receive-exact-u64:invented_length" yes no
                }
              other -> blockValue { llvmBlockTerminator = other })
            artifact
    in case verifyLLVMEmission context (recognizedRecordArtifact bundle) bad of
        Left LLVMOrdinaryTerminatorMismatch {} -> True
        _ -> False
  _ -> False

lookupSystemsBlock :: Text -> Text -> SystemsArtifact -> Maybe SystemsBlock
lookupSystemsBlock functionName blockName artifact = do
  functionValue <- Map.lookup functionName
    (systemsProgramFunctions (systemsArtifactProgram artifact))
  Map.lookup (BlockId blockName) (systemsFunctionBlocks functionValue)

adjustSystemsBlock
  :: Text
  -> Text
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
  -> SystemsArtifact
adjustSystemsBlock functionName blockName modify artifact = artifact
  { systemsArtifactProgram = program
      { systemsProgramFunctions = Map.adjust adjustFunction
          functionName (systemsProgramFunctions program) }
  }
  where
    program = systemsArtifactProgram artifact
    adjustFunction functionValue = functionValue
      { systemsFunctionBlocks = Map.adjust modify
          (BlockId blockName) (systemsFunctionBlocks functionValue) }

adjustLLVMBlock
  :: Text
  -> Text
  -> (LLVMBlock -> LLVMBlock)
  -> LLVMArtifact
  -> LLVMArtifact
adjustLLVMBlock functionName blockName modify artifact = artifact
  { llvmArtifactModule = moduleValue
      { llvmFunctions = Map.adjust adjustFunction functionName (llvmFunctions moduleValue) }
  }
  where
    moduleValue = llvmArtifactModule artifact
    adjustFunction functionValue = functionValue
      { llvmFunctionBlocks = Map.adjust modify
          (LLVMBlockId blockName) (llvmFunctionBlocks functionValue) }

rebindLLVMArtifact :: LLVMArtifact -> LLVMArtifact
rebindLLVMArtifact artifact = artifact
  { llvmArtifactText = renderLLVMModule moduleValue
  , llvmArtifactContract = contract { llvmContractTargetDigest = llvmModuleDigest moduleValue }
  }
  where
    moduleValue = llvmArtifactModule artifact
    contract = llvmArtifactContract artifact

test :: String -> Bool -> IO Bool
test label result = do
  putStrLn ((if result then "PASS " else "FAIL ") <> label)
  pure result
