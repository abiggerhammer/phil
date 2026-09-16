{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsStorage)
import Phil.LLVM.Storage
  ( phase0StorageLLVMTarget
  , phase0StorageLLVMVerificationContext
  )
import Phil.LLVM.Verify
  ( LLVMVerificationError (..)
  , verifyLLVMEmissionWith
  )
import Phil.Systems.IR (SystemsArtifact)
import Phil.Systems.Storage
  ( StorageBundle (..)
  , phase0StorageBundle
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testCase "R3 unchanged closed-world function coverage passes" unchangedPasses
    , testCase "R3 unadvertised extra target function rejects" unadvertisedExtraRejects
    , testCase "R3 selected lowerer may explicitly admit helper function" admittedExtraPasses
    ]
  if and results then pure () else exitFailure

unchangedPasses :: Bool
unchangedPasses = withFixture $ \bundle systemsArtifact llvmArtifact ->
  verifyLLVMEmissionWith
    lowerSystemsStorage
    (phase0StorageLLVMVerificationContext bundle)
    systemsArtifact
    llvmArtifact
    == Right ()

unadvertisedExtraRejects :: Bool
unadvertisedExtraRejects = withFixture $ \bundle systemsArtifact llvmArtifact ->
  let badArtifact = addExplicitHelper llvmArtifact
  in case verifyLLVMEmissionWith
      lowerSystemsStorage
      (phase0StorageLLVMVerificationContext bundle)
      systemsArtifact
      badArtifact of
    Left (LLVMFunctionSetMismatch expected actual) ->
      helperFunctionName `notElem` expected
        && helperFunctionName `elem` actual
    _ -> False

admittedExtraPasses :: Bool
admittedExtraPasses = case phase0StorageBundle of
  Left _ -> False
  Right bundle ->
    let systemsArtifact = storageArtifact bundle
        llvmArtifact = lowerSystemsStorageWithHelper
          phase0StorageLLVMTarget
          systemsArtifact
    in verifyLLVMEmissionWith
        lowerSystemsStorageWithHelper
        (phase0StorageLLVMVerificationContext bundle)
        systemsArtifact
        llvmArtifact
        == Right ()

withFixture
  :: (StorageBundle -> SystemsArtifact -> LLVMArtifact -> Bool)
  -> Bool
withFixture action = case phase0StorageBundle of
  Left _ -> False
  Right bundle ->
    let systemsArtifact = storageArtifact bundle
        llvmArtifact = lowerSystemsStorage phase0StorageLLVMTarget systemsArtifact
    in action bundle systemsArtifact llvmArtifact

lowerSystemsStorageWithHelper
  :: LLVMTargetProfile
  -> SystemsArtifact
  -> LLVMArtifact
lowerSystemsStorageWithHelper target systemsArtifact =
  addExplicitHelper (lowerSystemsStorage target systemsArtifact)

addExplicitHelper :: LLVMArtifact -> LLVMArtifact
addExplicitHelper artifact = rebindModule changedModule artifact
  where
    moduleValue = llvmArtifactModule artifact
    changedModule = moduleValue
      { llvmFunctions = Map.insert
          helperFunctionName
          helperFunction
          (llvmFunctions moduleValue)
      }

helperFunctionName :: Text
helperFunctionName = "review.r3.explicit.helper"

helperEntry :: LLVMBlockId
helperEntry = LLVMBlockId "review.r3.helper.entry"

helperFunction :: LLVMFunction
helperFunction = LLVMFunction
  { llvmFunctionName = helperFunctionName
  , llvmFunctionParameters = []
  , llvmFunctionEntry = helperEntry
  , llvmFunctionBlocks = Map.singleton helperEntry helperBlock
  }

helperBlock :: LLVMBlock
helperBlock = LLVMBlock
  { llvmBlockId = helperEntry
  , llvmBlockOps = []
  , llvmBlockTerminator = LLVMReturn "review-r3-explicit-helper"
  }

rebindModule :: LLVMModule -> LLVMArtifact -> LLVMArtifact
rebindModule moduleValue artifact = artifact
  { llvmArtifactModule = moduleValue
  , llvmArtifactText = renderLLVMModule moduleValue
  , llvmArtifactContract = contract
      { llvmContractTargetDigest = llvmModuleDigest moduleValue }
  }
  where
    contract = llvmArtifactContract artifact

testCase :: String -> Bool -> IO Bool
testCase label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
