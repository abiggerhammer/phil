{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.LLVM.IR
import Phil.LLVM.ServerFramedIngress (verifyServerFramedIngressLLVMWitnesses)
import Phil.LLVM.StorageFailureDetail
import Phil.Systems.IR
import Phil.Systems.StorageFailure
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "storage-failure-detail translation verifies" currentCandidateVerifies
    , test "proof-bound server framed-ingress predecessor remains preserved" predecessorPreserved
    , test "detailed store preserves exact source-derived operands and branches" detailedStoreExact
    , test "both store result slots are initialized exactly once before the provider call" outputSlotsInitialized
    , test "storage failure forwards exact error on exact transport and terminates fatally" failureFlowExact
    , test "wrong storage-error output identity is rejected" wrongStoreErrorRejects
    , test "wrong storage-failure transport identity is rejected" wrongFailureTransportRejects
    , test "missing output-slot initialization is rejected" missingSlotInitializationRejects
    , test "post-transfer payload reuse on storage failure is rejected" postTransferPayloadReuseRejects
    , test "ambient storage state is rejected" ambientStateRejects
    , test "legacy storage-failure residue is rejected" legacyResidueRejects
    ]
  if and results then pure () else exitFailure

currentCandidateVerifies :: Bool
currentCandidateVerifies = verifyPhase0StorageFailureDetailLLVM == Right ()

predecessorPreserved :: Bool
predecessorPreserved = withCandidate $ \bundle artifact ->
  isRight (verifyServerFramedIngressLLVMWitnesses (storageFailurePredecessor bundle) artifact)

detailedStoreExact :: Bool
detailedStoreExact = withCandidate $ \bundle artifact -> doBool $ do
  let witness = storageFailureWitness bundle
      systemsProgram = systemsArtifactProgram (storageFailureArtifact bundle)
  systemsFunction <- Map.lookup
    (storageFailureFunction witness)
    (systemsProgramFunctions systemsProgram)
  systemsStore <- Map.lookup
    (storageFailureStoreBlock witness)
    (systemsFunctionBlocks systemsFunction)
  (owner, uploadId, site, success, failure) <- case systemsBlockTerminator systemsStore of
    TermStore p u s yes no -> Just (p, u, s, yes, no)
    _ -> Nothing
  llvmFunction <- Map.lookup
    (storageFailureFunction witness)
    (llvmFunctions (llvmArtifactModule artifact))
  llvmStore <- Map.lookup
    (LLVMBlockId (unBlockId (storageFailureStoreBlock witness)))
    (llvmFunctionBlocks llvmFunction)
  pure $ llvmBlockTerminator llvmStore ==
    LLVMStoreDetailed
      site
      (unValueId owner <> ".owner")
      (unValueId uploadId)
      (unValueId (storageFailureErrorValue witness))
      (LLVMBlockId (unBlockId success))
      (LLVMBlockId (unBlockId failure))

outputSlotsInitialized :: Bool
outputSlotsInitialized = withCandidate $ \bundle artifact ->
  let witness = storageFailureWitness bundle
      uploadSlot =
        "store ptr null, ptr %phil_store_upload_slot_" <>
        symbolish (unValueId (storageFailureSuccessResult witness))
      errorSlot =
        "store ptr null, ptr %phil_store_error_slot_" <>
        symbolish (unValueId (storageFailureErrorValue witness))
      rendered = llvmArtifactText artifact
  in countOccurrences uploadSlot rendered == 1
      && countOccurrences errorSlot rendered == 1

failureFlowExact :: Bool
failureFlowExact = withCandidate $ \bundle artifact -> doBool $ do
  let witness = storageFailureWitness bundle
  llvmFunction <- Map.lookup
    (storageFailureFunction witness)
    (llvmFunctions (llvmArtifactModule artifact))
  failure <- Map.lookup
    (LLVMBlockId (unBlockId (storageFailureFailureBlock witness)))
    (llvmFunctionBlocks llvmFunction)
  pure $
    llvmBlockOps failure ==
      [ LLVMStorageFailureEffect
          (unValueId (storageFailureTransport witness))
          (unValueId (storageFailureErrorValue witness))
      ]
    && llvmBlockTerminator failure ==
      LLVMReturn ("fatal:" <> storageFailureFatalClass witness)

wrongStoreErrorRejects :: Bool
wrongStoreErrorRejects = withCandidate $ \bundle artifact ->
  let witness = storageFailureWitness bundle
      blockId = LLVMBlockId (unBlockId (storageFailureStoreBlock witness))
      mutated = mutateServerBlock blockId mutateTerm artifact
      mutateTerm blockValue = blockValue
        { llvmBlockTerminator = case llvmBlockTerminator blockValue of
            LLVMStoreDetailed site payload uploadId _storageError yes no ->
              LLVMStoreDetailed site payload uploadId "wrong.storage.error" yes no
            other -> other
        }
  in isLeft (verifyStorageFailureDetailTranslation bundle mutated)

wrongFailureTransportRejects :: Bool
wrongFailureTransportRejects = withCandidate $ \bundle artifact ->
  let witness = storageFailureWitness bundle
      blockId = LLVMBlockId (unBlockId (storageFailureFailureBlock witness))
      mutateOp operation = case operation of
        LLVMStorageFailureEffect _transport storageError ->
          LLVMStorageFailureEffect "wrong.server.transport" storageError
        other -> other
      mutated = mutateServerBlock blockId
        (\blockValue -> blockValue { llvmBlockOps = map mutateOp (llvmBlockOps blockValue) })
        artifact
  in isLeft (verifyStorageFailureDetailTranslation bundle mutated)

missingSlotInitializationRejects :: Bool
missingSlotInitializationRejects = withCandidate $ \bundle artifact ->
  let witness = storageFailureWitness bundle
      needle =
        "store ptr null, ptr %phil_store_error_slot_" <>
        symbolish (unValueId (storageFailureErrorValue witness))
      mutated = artifact
        { llvmArtifactText = Text.replace needle "; removed required null initialization" (llvmArtifactText artifact) }
  in isLeft (verifyStorageFailureDetailTranslation bundle mutated)

postTransferPayloadReuseRejects :: Bool
postTransferPayloadReuseRejects = withCandidate $ \bundle artifact ->
  let witness = storageFailureWitness bundle
      blockId = LLVMBlockId (unBlockId (storageFailureFailureBlock witness))
      payload = unValueId (storageFailureOwner witness) <> ".owner"
      mutated = mutateServerBlock blockId
        (\blockValue -> blockValue
          { llvmBlockOps = llvmBlockOps blockValue <>
              [LLVMPlain ("observe transferred payload " <> payload)]
          })
        artifact
  in isLeft (verifyStorageFailureDetailTranslation bundle mutated)

ambientStateRejects :: Bool
ambientStateRejects = withCandidate $ \bundle artifact ->
  let mutated = artifact
        { llvmArtifactText = llvmArtifactText artifact <> "\ncurrent_storage_error\n" }
  in isLeft (verifyStorageFailureDetailTranslation bundle mutated)

legacyResidueRejects :: Bool
legacyResidueRejects = withCandidate $ \bundle artifact ->
  let mutated = artifact
        { llvmArtifactText = llvmArtifactText artifact <>
            "\n@phil_runtime_store(ptr %server_payload_owner)\n" }
  in isLeft (verifyStorageFailureDetailTranslation bundle mutated)

mutateServerBlock
  :: LLVMBlockId
  -> (LLVMBlock -> LLVMBlock)
  -> LLVMArtifact
  -> LLVMArtifact
mutateServerBlock blockId transform artifact =
  let moduleValue = llvmArtifactModule artifact
      functions' = Map.adjust
        (\function -> function
          { llvmFunctionBlocks = Map.adjust transform blockId (llvmFunctionBlocks function) })
        "UploadServer"
        (llvmFunctions moduleValue)
  in artifact { llvmArtifactModule = moduleValue { llvmFunctions = functions' } }

withCandidate :: (StorageFailureBundle -> LLVMArtifact -> Bool) -> Bool
withCandidate action = case phase0StorageFailureBundle of
  Left _ -> False
  Right bundle ->
    let artifact = lowerSystemsStorageFailureDetail
          phase0StorageFailureDetailLLVMTarget
          (storageFailureArtifact bundle)
    in action bundle artifact

countOccurrences :: Text -> Text -> Int
countOccurrences needle haystack
  | Text.null needle = 0
  | otherwise = go haystack
  where
    go remaining = case Text.breakOn needle remaining of
      (_, suffix) | Text.null suffix -> 0
      (_, suffix) -> 1 + go (Text.drop (Text.length needle) suffix)

symbolish :: Text -> Text
symbolish = Text.map (\character ->
  if ('a' <= character && character <= 'z')
      || ('A' <= character && character <= 'Z')
      || ('0' <= character && character <= '9')
    then character
    else '_')

isLeft :: Either a b -> Bool
isLeft value = case value of
  Left _ -> True
  Right _ -> False

isRight :: Either a b -> Bool
isRight value = case value of
  Left _ -> False
  Right _ -> True

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
