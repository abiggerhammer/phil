{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "digest-validation Systems candidate verifies" systemsCandidatePasses
    , test "digest-validation LLVM candidate verifies" llvmCandidatePasses
    , test "digest-validation certification closes" certificationPasses
    , test "missing Begin digest subject is rejected" missingBeginSubjectRejects
    , test "wrong payload borrow owner is rejected" wrongBorrowOwnerRejects
    , test "swapped digest LLVM operands are rejected" swappedOperandsRejects
    , test "wrong digest LLVM record identity is rejected" wrongRecordRejects
    , test "wrong digest LLVM payload identity is rejected" wrongPayloadRejects
    ]
  if and results then pure () else exitFailure

systemsCandidatePasses :: Bool
systemsCandidatePasses = case phase0DigestValidationBundle of
  Right _ -> True
  Left _ -> False

llvmCandidatePasses :: Bool
llvmCandidatePasses = verifyPhase0DigestValidationLLVM == Right ()

certificationPasses :: Bool
certificationPasses = verifyPhase0DigestValidationLLVMCertification == Right ()

missingBeginSubjectRejects :: Bool
missingBeginSubjectRejects = withDigestBundle $ \bundle ->
  let artifact = digestValidationArtifact bundle
      witness = digestValidationWitness bundle
      badArtifact = mapSystemsBlock
        (digestValidationFunction witness)
        (digestValidationBlock witness)
        (\blockValue -> blockValue
          { systemsBlockTerminator = case systemsBlockTerminator blockValue of
              terminator@TermRuntimeCheck {} -> terminator
                { checkInputs = [digestValidationPayloadView witness] }
              other -> other
          })
        artifact
  in case verifyDigestValidationWitness badArtifact witness of
    Left (DigestValidationCheckMismatch "UploadServer" _ _) -> True
    _ -> False

wrongBorrowOwnerRejects :: Bool
wrongBorrowOwnerRejects = withDigestBundle $ \bundle ->
  let artifact = digestValidationArtifact bundle
      witness = digestValidationWitness bundle
      badArtifact = mapSystemsFunction
        (digestValidationFunction witness)
        (\function -> function
          { systemsFunctionValues = Map.adjust
              (\value -> value
                { systemsValueRole = BorrowedSlice (ValueId "server.frame.begin") })
              (digestValidationPayloadView witness)
              (systemsFunctionValues function)
          })
        artifact
  in case verifyDigestValidationWitness badArtifact witness of
    Left (DigestValidationViewRoleMismatch "UploadServer" _ _ _) -> True
    _ -> False

swappedOperandsRejects :: Bool
swappedOperandsRejects = withDigestLLVM $ \bundle artifact ->
  let witness = digestValidationWitness bundle
      badArtifact = mapLLVMBlock
        (digestValidationFunction witness)
        (LLVMBlockId (unBlockId (digestValidationBlock witness)))
        (mapDigest $ \site record payload yes no ->
          LLVMDigestValidate site payload record yes no)
        artifact
  in case verifyDigestValidationTranslation bundle badArtifact of
    Left (DigestValidationTerminatorMismatch "UploadServer" _ _) -> True
    _ -> False

wrongRecordRejects :: Bool
wrongRecordRejects = withDigestLLVM $ \bundle artifact ->
  let witness = digestValidationWitness bundle
      badArtifact = mapLLVMBlock
        (digestValidationFunction witness)
        (LLVMBlockId (unBlockId (digestValidationBlock witness)))
        (mapDigest $ \site _ payload yes no ->
          LLVMDigestValidate site "server.wrong_begin" payload yes no)
        artifact
  in case verifyDigestValidationTranslation bundle badArtifact of
    Left (DigestValidationTerminatorMismatch "UploadServer" _ _) -> True
    _ -> False

wrongPayloadRejects :: Bool
wrongPayloadRejects = withDigestLLVM $ \bundle artifact ->
  let witness = digestValidationWitness bundle
      badArtifact = mapLLVMBlock
        (digestValidationFunction witness)
        (LLVMBlockId (unBlockId (digestValidationBlock witness)))
        (mapDigest $ \site record _ yes no ->
          LLVMDigestValidate site record "server.wrong_payload.owner" yes no)
        artifact
  in case verifyDigestValidationTranslation bundle badArtifact of
    Left (DigestValidationTerminatorMismatch "UploadServer" _ _) -> True
    _ -> False

withDigestBundle :: (DigestValidationBundle -> Bool) -> Bool
withDigestBundle action = case phase0DigestValidationBundle of
  Left _ -> False
  Right bundle -> action bundle

withDigestLLVM
  :: (DigestValidationBundle -> LLVMArtifact -> Bool)
  -> Bool
withDigestLLVM action = withDigestBundle $ \bundle ->
  action bundle (lowerSystemsDigestValidation
    phase0DigestValidationLLVMTarget
    (digestValidationArtifact bundle))

mapDigest
  :: ( RuntimeSiteRef
    -> Text
    -> Text
    -> LLVMBlockId
    -> LLVMBlockId
    -> LLVMTerminator
     )
  -> LLVMBlock
  -> LLVMBlock
mapDigest transform blockValue = blockValue
  { llvmBlockTerminator = case llvmBlockTerminator blockValue of
      LLVMDigestValidate site record payload yes no ->
        transform site record payload yes no
      other -> other
  }

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
