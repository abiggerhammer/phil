{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "storage Systems witness verifies" systemsCandidatePasses
    , test "storage LLVM candidate verifies" llvmCandidatePasses
    , test "storage certification closes" certificationPasses
    , test "storage ABI binds owner consumption" ownershipDescriptorBound
    , test "storage ABI keeps UploadId opaque" uploadIdDescriptorBound
    , test "wrong storage owner is rejected" wrongStoreOwnerRejects
    , test "wrong UploadId semantic role is rejected" wrongUploadIdRoleRejects
    , test "wrong LLVM storage owner is rejected" wrongLLVMStoreOwnerRejects
    , test "wrong LLVM UploadId identity is rejected" wrongLLVMUploadIdRejects
    , test "reserved storage status cannot become success" wrongRenderedStatusRejects
    , test "post-transfer payload release is rejected" postTransferReleaseRejects
    ]
  if and results then pure () else exitFailure

systemsCandidatePasses :: Bool
systemsCandidatePasses = case phase0StorageBundle of
  Right _ -> True
  Left _ -> False

llvmCandidatePasses :: Bool
llvmCandidatePasses = verifyPhase0StorageLLVM == Right ()

certificationPasses :: Bool
certificationPasses = verifyPhase0StorageLLVMCertification == Right ()

ownershipDescriptorBound :: Bool
ownershipDescriptorBound =
  Text.isInfixOf "store-ownership=consume-payload-on-all-outcomes" storageABIDescriptor
  && Text.isInfixOf "store-status=1-success,other-failure" storageABIDescriptor

uploadIdDescriptorBound :: Bool
uploadIdDescriptorBound =
  Text.isInfixOf "upload-id-handle=opaque-runtime-managed-nonowning" storageABIDescriptor
  && Text.isInfixOf "upload-id-layout-access=forbidden" storageABIDescriptor
  && Text.isInfixOf "upload-id-release=forbidden" storageABIDescriptor

wrongStoreOwnerRejects :: Bool
wrongStoreOwnerRejects = withStorageBundle $ \bundle ->
  let artifact = storageArtifact bundle
      witness = storageWitness bundle
      digestWitness = digestValidationWitness (storageDigestValidationBundle bundle)
      badArtifact = mapSystemsBlock
        (storageFunction witness)
        (storageBlock witness)
        (\blockValue -> blockValue
          { systemsBlockTerminator = case systemsBlockTerminator blockValue of
              term@TermStore {} -> term { storeOwner = ValueId "server.frame.begin" }
              other -> other
          })
        artifact
  in case verifyStorageWitness badArtifact digestWitness witness of
    Left (StorageTerminatorMismatch _ _ _) -> True
    _ -> False

wrongUploadIdRoleRejects :: Bool
wrongUploadIdRoleRejects = withStorageBundle $ \bundle ->
  let artifact = storageArtifact bundle
      witness = storageWitness bundle
      digestWitness = digestValidationWitness (storageDigestValidationBundle bundle)
      badArtifact = mapSystemsFunction
        (storageFunction witness)
        (\function -> function
          { systemsFunctionValues = Map.adjust
              (\value -> value { systemsValueRole = RuntimeScalar "NotUploadId" })
              (storageResult witness)
              (systemsFunctionValues function)
          })
        artifact
  in case verifyStorageWitness badArtifact digestWitness witness of
    Left (StorageResultRoleMismatch _ _ _) -> True
    _ -> False

wrongLLVMStoreOwnerRejects :: Bool
wrongLLVMStoreOwnerRejects = withStorageLLVM $ \bundle artifact ->
  let witness = storageWitness bundle
      badArtifact = mapLLVMBlock
        (storageFunction witness)
        (LLVMBlockId (unBlockId (storageBlock witness)))
        (mapStore $ \site _ uploadId yes no ->
          LLVMStore site "server.wrong_payload.owner" uploadId yes no)
        artifact
  in case verifyStorageTranslation bundle badArtifact of
    Left (StorageLLVMTerminatorMismatch _ _ _) -> True
    _ -> False

wrongLLVMUploadIdRejects :: Bool
wrongLLVMUploadIdRejects = withStorageLLVM $ \bundle artifact ->
  let witness = storageWitness bundle
      badArtifact = mapLLVMBlock
        (storageFunction witness)
        (LLVMBlockId (unBlockId (storageBlock witness)))
        (mapStore $ \site owner _ yes no ->
          LLVMStore site owner "server.wrong_upload_id" yes no)
        artifact
  in case verifyStorageTranslation bundle badArtifact of
    Left (StorageLLVMTerminatorMismatch _ _ _) -> True
    _ -> False

wrongRenderedStatusRejects :: Bool
wrongRenderedStatusRejects = withStorageLLVM $ \bundle artifact ->
  let badArtifact = artifact
        { llvmArtifactText = Text.replace
            "%phil_store_ok_server_store = icmp eq i8 %phil_store_status_server_store, 1"
            "%phil_store_ok_server_store = icmp eq i8 %phil_store_status_server_store, 2"
            (llvmArtifactText artifact)
        }
  in case verifyStorageTranslation bundle badArtifact of
    Left (StorageRenderedStatusMismatch "UploadServer") -> True
    _ -> False

postTransferReleaseRejects :: Bool
postTransferReleaseRejects = withStorageLLVM $ \bundle artifact ->
  let witness = storageWitness bundle
      successBlock = LLVMBlockId (unBlockId (storageSuccess witness))
      badArtifact = mapLLVMBlock
        (storageFunction witness)
        successBlock
        (\blockValue -> blockValue
          { llvmBlockOps = LLVMBufferRelease "server.payload.owner" : llvmBlockOps blockValue })
        artifact
  in case verifyStorageTranslation bundle badArtifact of
    Left (StoragePostTransferReleaseDetected _ _ _) -> True
    _ -> False

withStorageBundle :: (StorageBundle -> Bool) -> Bool
withStorageBundle action = case phase0StorageBundle of
  Left _ -> False
  Right bundle -> action bundle

withStorageLLVM :: (StorageBundle -> LLVMArtifact -> Bool) -> Bool
withStorageLLVM action = withStorageBundle $ \bundle ->
  action bundle (lowerSystemsStorage phase0StorageLLVMTarget (storageArtifact bundle))

mapStore
  :: (RuntimeSiteRef -> Text -> Text -> LLVMBlockId -> LLVMBlockId -> LLVMTerminator)
  -> LLVMBlock
  -> LLVMBlock
mapStore transform blockValue = blockValue
  { llvmBlockTerminator = case llvmBlockTerminator blockValue of
      LLVMStore site owner uploadId yes no -> transform site owner uploadId yes no
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
