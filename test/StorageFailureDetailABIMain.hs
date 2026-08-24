{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.LLVM
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "storage failure detail translation verifies" candidateVerifies
    , test "store exposes exact upload-id and storage-error outputs" detailedStoreExplicit
    , test "storage failure forwards exact error on exact transport" failureEffectExplicit
    , test "store output slots are initialized before provider call" slotsInitialized
    , test "legacy storage error materialization is absent" legacyStorageFailureAbsent
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = verifyPhase0StorageFailureDetailLLVM == Right ()

detailedStoreExplicit :: Bool
detailedStoreExplicit = withCandidate $ \artifact -> doBool $ do
  server <- Map.lookup "UploadServer" (llvmFunctions (llvmArtifactModule artifact))
  storeBlock <- Map.lookup (LLVMBlockId "server.store") (llvmFunctionBlocks server)
  pure $ case llvmBlockTerminator storeBlock of
    LLVMStoreDetailed _ payload uploadId storageError _ _ ->
      payload == "server.payload.owner"
        && uploadId == "server.upload_id"
        && storageError == "server.storage_error"
    _ -> False

failureEffectExplicit :: Bool
failureEffectExplicit = withCandidate $ \artifact -> doBool $ do
  server <- Map.lookup "UploadServer" (llvmFunctions (llvmArtifactModule artifact))
  failure <- Map.lookup (LLVMBlockId "server.storage_failure") (llvmFunctionBlocks server)
  pure $
    llvmBlockOps failure ==
      [LLVMStorageFailureEffect "server.transport" "server.storage_error"]
    && llvmBlockTerminator failure == LLVMReturn "fatal:StorageFailure"

slotsInitialized :: Bool
slotsInitialized = withCandidate $ \artifact ->
  let rendered = llvmArtifactText artifact
  in Text.isInfixOf "store ptr null, ptr %phil_store_upload_slot_server_upload_id" rendered
      && Text.isInfixOf "store ptr null, ptr %phil_store_error_slot_server_storage_error" rendered

legacyStorageFailureAbsent :: Bool
legacyStorageFailureAbsent = withCandidate $ \artifact ->
  let rendered = llvmArtifactText artifact
  in all (not . (`Text.isInfixOf` rendered))
      [ "@phil_runtime_store(ptr %server_payload_owner)"
      , "@phil_call_materialize_storage_failure_error()"
      , "@phil_call_fail_internal_storage()"
      , "current_storage_error"
      , "current_storage_payload"
      ]

withCandidate :: (LLVMArtifact -> Bool) -> Bool
withCandidate action = case phase0StorageFailureDetailLLVMArtifact of
  Left _ -> False
  Right artifact -> action artifact

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
