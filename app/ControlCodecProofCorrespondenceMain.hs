{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Assurance.Types (digestText)
import Phil.LLVM.ControlCodec
import Phil.LLVM.IR
import Phil.LLVM.StorageFailureDetail
import Phil.Systems.StorageFailure
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "control-codec translation verifies" currentCandidateVerifies
    , test "control-codec preserves predecessor function bodies and strengthenings exactly" predecessorStructureExact
    , test "control-codec runtime profile and descriptor digest are exact" profileAndDescriptorExact
    , test "required predecessor primitives remain explicitly rendered" requiredPrimitivesPresent
    , test "function-body drift is rejected" functionBodyDriftRejects
    , test "runtime-profile drift is rejected" profileDriftRejects
    , test "runtime-ABI digest drift is rejected" abiDigestDriftRejects
    , test "legacy storage-failure runtime-profile residue is rejected" legacyProfileResidueRejects
    ]
  if and results then pure () else exitFailure

currentCandidateVerifies :: Bool
currentCandidateVerifies = verifyPhase0ControlCodecLLVM == Right ()

predecessorStructureExact :: Bool
predecessorStructureExact = withCandidate $ \bundle artifact ->
  let systemsArtifact = storageFailureArtifact bundle
      predecessor = lowerSystemsStorageFailureDetail
        phase0StorageFailureDetailLLVMTarget
        systemsArtifact
      predecessorModule = llvmArtifactModule predecessor
      moduleValue = llvmArtifactModule artifact
  in llvmFunctions moduleValue == llvmFunctions predecessorModule
      && llvmStrengthenings moduleValue == llvmStrengthenings predecessorModule

profileAndDescriptorExact :: Bool
profileAndDescriptorExact = withCandidate $ \_ artifact ->
  let moduleValue = llvmArtifactModule artifact
  in llvmRuntimeABIProfile moduleValue == "phil-runtime/phase0/control-codec-v1"
      && llvmRuntimeABIDigest moduleValue == digestText controlCodecABIDescriptor
      && all (`Text.isInfixOf` controlCodecABIDescriptor)
        [ "frame.magic=50:48:49:4c"
        , "frame.codec-version=01"
        , "frame.tag.Hello=01"
        , "frame.tag.Begin=02"
        , "hello.canonical=strictly-increasing-versions"
        , "begin.digest-alg.sha256=01"
        , "integer-byte-order=big-endian"
        , "codec-provider=single-shared-client-encoder/server-decoder-implementation"
        ]

requiredPrimitivesPresent :: Bool
requiredPrimitivesPresent = withCandidate $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (`Text.isInfixOf` rendered)
      [ "declare void @phil_runtime_send_hello(ptr, ptr)"
      , "declare void @phil_runtime_send_begin_sha256(ptr, i64, ptr, ptr)"
      , "declare void @phil_runtime_receive_frame_Hello(ptr, ptr, ptr)"
      , "declare void @phil_runtime_receive_frame_Begin(ptr, ptr, ptr)"
      , "declare i8 @phil_runtime_recognize_Hello(ptr, ptr, ptr, ptr)"
      , "declare i8 @phil_runtime_recognize_Begin(ptr, ptr, ptr, ptr)"
      , "declare i8 @phil_runtime_store_with_error(ptr, ptr, ptr)"
      ]

functionBodyDriftRejects :: Bool
functionBodyDriftRejects = withCandidate $ \bundle artifact ->
  let moduleValue = llvmArtifactModule artifact
      functions' = fmap mutateFunction (llvmFunctions moduleValue)
      mutated = artifact { llvmArtifactModule = moduleValue { llvmFunctions = functions' } }
  in isLeft (verifyControlCodecTranslation bundle mutated)
  where
    mutateFunction functionValue = functionValue
      { llvmFunctionBlocks = fmap mutateBlock (llvmFunctionBlocks functionValue) }
    mutateBlock blockValue = blockValue
      { llvmBlockOps = LLVMMetadata "control-codec-proof-drift" : llvmBlockOps blockValue }

profileDriftRejects :: Bool
profileDriftRejects = withCandidate $ \bundle artifact ->
  let moduleValue = llvmArtifactModule artifact
      mutated = artifact
        { llvmArtifactModule = moduleValue
            { llvmRuntimeABIProfile = "phil-runtime/phase0/storage-failure-detail-v1" }
        }
  in isLeft (verifyControlCodecTranslation bundle mutated)

abiDigestDriftRejects :: Bool
abiDigestDriftRejects = withCandidate $ \bundle artifact ->
  let moduleValue = llvmArtifactModule artifact
      mutated = artifact
        { llvmArtifactModule = moduleValue
            { llvmRuntimeABIDigest = digestText "wrong-control-codec-abi" }
        }
  in isLeft (verifyControlCodecTranslation bundle mutated)

legacyProfileResidueRejects :: Bool
legacyProfileResidueRejects = withCandidate $ \bundle artifact ->
  let mutated = artifact
        { llvmArtifactText = llvmArtifactText artifact <>
            "\n; runtime-abi-profile=phil-runtime/phase0/storage-failure-detail-v1\n"
        }
  in isLeft (verifyControlCodecTranslation bundle mutated)

withCandidate :: (StorageFailureBundle -> LLVMArtifact -> Bool) -> Bool
withCandidate action = case phase0StorageFailureBundle of
  Left _ -> False
  Right bundle ->
    let artifact = lowerSystemsControlCodec
          phase0ControlCodecLLVMTarget
          (storageFailureArtifact bundle)
    in action bundle artifact

isLeft :: Either a b -> Bool
isLeft value = case value of
  Left _ -> True
  Right _ -> False

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
