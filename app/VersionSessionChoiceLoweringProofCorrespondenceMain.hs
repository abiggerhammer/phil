{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.LLVM
import Phil.LLVM.VersionSessionChoiceLoweringProofCheck
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "exact version-choice lowering proof witness verifies" candidateVerifies
    , test "duplicate Systems materialization is rejected" duplicateMaterializeRejects
    , test "duplicate Systems version select is rejected" duplicateSystemsVersionSelectRejects
    , test "duplicate LLVM unsupported selector is rejected" duplicateLLVMUnsupportedRejects
    , test "duplicate LLVM version selector is rejected" duplicateLLVMVersionRejects
    , test "duplicate LLVM client payload binding is rejected" duplicateLLVMClientBindingRejects
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = withCandidate $ \bundle llvmArtifact ->
  verifyVersionSessionChoiceLoweringProofWitness bundle llvmArtifact == Right ()

duplicateMaterializeRejects :: Bool
duplicateMaterializeRejects = withCandidate $ \bundle llvmArtifact ->
  let witness = versionChoiceOperandsWitness bundle
      artifact = versionChoiceOperandsArtifact bundle
      mutated = mapSystemsBlock artifact "UploadServer"
        (versionOperandsHelloCommitBlock witness) $ \blockValue ->
          blockValue { systemsBlockOps = duplicateFirst isMaterialize (systemsBlockOps blockValue) }
      isMaterialize operation = case operation of
        OpRuntimeCall name _ _ _ _ -> name == versionOperandsMaterializeCall witness
        _ -> False
  in case verifyVersionSessionChoiceLoweringExactShape mutated witness llvmArtifact of
      Left (VersionLoweringProofSystemsMaterializeMultiplicity 2) -> True
      _ -> False

duplicateSystemsVersionSelectRejects :: Bool
duplicateSystemsVersionSelectRejects = withCandidate $ \bundle llvmArtifact ->
  let witness = versionChoiceOperandsWitness bundle
      versionWitness = phase0VersionSessionChoiceWitness
      artifact = versionChoiceOperandsArtifact bundle
      mutated = mapSystemsBlock artifact "UploadServer"
        (versionChoiceServerVersionBlock versionWitness) $ \blockValue ->
          blockValue { systemsBlockOps = duplicateFirst isVersionSelect (systemsBlockOps blockValue) }
      isVersionSelect operation = case operation of
        OpSessionSelect transport label payload decision ->
          transport == versionChoiceServerTransport versionWitness
            && label == versionChoiceVersionLabel versionWitness
            && payload == Just (versionChoiceServerSelectedVersion versionWitness)
            && decision == versionChoiceSelectDecision versionWitness
        _ -> False
  in case verifyVersionSessionChoiceLoweringExactShape mutated witness llvmArtifact of
      Left (VersionLoweringProofSystemsVersionSelectMultiplicity 2) -> True
      _ -> False

duplicateLLVMUnsupportedRejects :: Bool
duplicateLLVMUnsupportedRejects = withCandidate $ \bundle llvmArtifact ->
  let witness = versionChoiceOperandsWitness bundle
      versionWitness = phase0VersionSessionChoiceWitness
      blockId = LLVMBlockId (unBlockId (versionChoiceServerUnsupportedBlock versionWitness))
      transport = unValueId (versionChoiceServerTransport versionWitness)
      mutated = mapLLVMBlock llvmArtifact "UploadServer" blockId $ \blockValue ->
        blockValue { llvmBlockOps = duplicateFirst (== LLVMUnsupportedSelect transport) (llvmBlockOps blockValue) }
  in case verifyVersionSessionChoiceLoweringExactShape
      (versionChoiceOperandsArtifact bundle) witness mutated of
      Left (VersionLoweringProofLLVMUnsupportedSelectMultiplicity 2) -> True
      _ -> False

duplicateLLVMVersionRejects :: Bool
duplicateLLVMVersionRejects = withCandidate $ \bundle llvmArtifact ->
  let witness = versionChoiceOperandsWitness bundle
      versionWitness = phase0VersionSessionChoiceWitness
      blockId = LLVMBlockId (unBlockId (versionChoiceServerVersionBlock versionWitness))
      transport = unValueId (versionChoiceServerTransport versionWitness)
      selected = unValueId (versionOperandsSelectedVersion witness)
      mutated = mapLLVMBlock llvmArtifact "UploadServer" blockId $ \blockValue ->
        blockValue { llvmBlockOps = duplicateFirst (== LLVMVersionSelect transport selected) (llvmBlockOps blockValue) }
  in case verifyVersionSessionChoiceLoweringExactShape
      (versionChoiceOperandsArtifact bundle) witness mutated of
      Left (VersionLoweringProofLLVMVersionSelectMultiplicity 2) -> True
      _ -> False

duplicateLLVMClientBindingRejects :: Bool
duplicateLLVMClientBindingRejects = withCandidate $ \bundle llvmArtifact ->
  let witness = versionChoiceOperandsWitness bundle
      versionWitness = phase0VersionSessionChoiceWitness
      blockId = LLVMBlockId (unBlockId (versionChoiceClientVersionTarget versionWitness))
      selected = unValueId (versionChoiceClientSelectedVersion versionWitness)
      mutated = mapLLVMBlock llvmArtifact "UploadClient" blockId $ \blockValue ->
        blockValue { llvmBlockOps = duplicateFirst (== LLVMVersionChoicePayloadBinding selected) (llvmBlockOps blockValue) }
  in case verifyVersionSessionChoiceLoweringExactShape
      (versionChoiceOperandsArtifact bundle) witness mutated of
      Left (VersionLoweringProofLLVMClientBindingMultiplicity 2) -> True
      _ -> False

withCandidate :: (VersionChoiceOperandsBundle -> LLVMArtifact -> Bool) -> Bool
withCandidate action = case phase0VersionChoiceOperandsBundle of
  Left _ -> False
  Right bundle ->
    let llvmArtifact = lowerSystemsVersionSessionChoice
          phase0VersionSessionChoiceLLVMTarget
          (versionChoiceOperandsArtifact bundle)
    in action bundle llvmArtifact

duplicateFirst :: (a -> Bool) -> [a] -> [a]
duplicateFirst predicate values =
  case break predicate values of
    (before, value : after) -> before <> [value, value] <> after
    _ -> values

mapSystemsBlock
  :: SystemsArtifact
  -> Text
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapSystemsBlock artifact functionName blockId transform =
  let program = systemsArtifactProgram artifact
      functions = systemsProgramFunctions program
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks = Map.adjust transform blockId (systemsFunctionBlocks function) })
        functionName
        functions
  in artifact { systemsArtifactProgram = program { systemsProgramFunctions = functions' } }

mapLLVMBlock
  :: LLVMArtifact
  -> Text
  -> LLVMBlockId
  -> (LLVMBlock -> LLVMBlock)
  -> LLVMArtifact
mapLLVMBlock artifact functionName blockId transform =
  let moduleValue = llvmArtifactModule artifact
      functions = llvmFunctions moduleValue
      functions' = Map.adjust
        (\function -> function
          { llvmFunctionBlocks = Map.adjust transform blockId (llvmFunctionBlocks function) })
        functionName
        functions
  in artifact { llvmArtifactModule = moduleValue { llvmFunctions = functions' } }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
