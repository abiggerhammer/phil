{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.Storage
  ( StorageWitness (..)
  , StorageBundle (..)
  , StorageError (..)
  , phase0StorageWitness
  , phase0StorageBundle
  , verifyStorageBundle
  , verifyStorageWitness
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Systems.DigestValidation
import Phil.Systems.IR
import Phil.Systems.Verify (SystemsVerificationContext)

-- Storage is already explicit in the digest-validation Systems artifact. This
-- layer does not mutate that artifact; it names and verifies the storage
-- boundary so the next target representation can be certified independently.
data StorageWitness = StorageWitness
  { storageFunction :: Text
  , storageBlock :: BlockId
  , storageOwner :: ValueId
  , storageResult :: ValueId
  , storageSuccess :: BlockId
  , storageFailure :: BlockId
  }
  deriving (Eq, Show)

data StorageBundle = StorageBundle
  { storageArtifact :: SystemsArtifact
  , storageContext :: SystemsVerificationContext
  , storageDigestValidationBundle :: DigestValidationBundle
  , storageWitness :: StorageWitness
  }
  deriving (Eq, Show)

data StorageError
  = StorageDigestValidationError DigestValidationError
  | StorageFunctionMissing Text
  | StorageBlockMissing Text BlockId
  | StorageOwnerMissing Text ValueId
  | StorageOwnerRoleMismatch Text ValueId SystemsValueRole
  | StorageResultMissing Text ValueId
  | StorageResultRoleMismatch Text ValueId SystemsValueRole
  | StorageTerminatorMismatch Text BlockId SystemsTerminator
  | StorageMultiplicityMismatch Text ValueId Int
  | StorageDigestPredecessorMismatch Text BlockId SystemsTerminator
  | StorageExplicitReleaseAfterTransfer Text BlockId ValueId
  deriving (Eq, Show)

phase0StorageWitness :: StorageWitness
phase0StorageWitness = StorageWitness
  { storageFunction = "UploadServer"
  , storageBlock = BlockId "server.store"
  , storageOwner = ValueId "server.payload"
  , storageResult = ValueId "server.upload_id"
  , storageSuccess = BlockId "server.accepted"
  , storageFailure = BlockId "server.storage_failure"
  }

phase0StorageBundle :: Either StorageError StorageBundle
phase0StorageBundle = do
  digestBundle <- mapLeft StorageDigestValidationError phase0DigestValidationBundle
  let bundle = StorageBundle
        { storageArtifact = digestValidationArtifact digestBundle
        , storageContext = digestValidationContext digestBundle
        , storageDigestValidationBundle = digestBundle
        , storageWitness = phase0StorageWitness
        }
  verifyStorageBundle bundle
  pure bundle

verifyStorageBundle :: StorageBundle -> Either StorageError ()
verifyStorageBundle bundle = do
  mapLeft StorageDigestValidationError $
    verifyDigestValidationBundle (storageDigestValidationBundle bundle)
  verifyStorageWitness
    (storageArtifact bundle)
    (digestValidationWitness (storageDigestValidationBundle bundle))
    (storageWitness bundle)

verifyStorageWitness
  :: SystemsArtifact
  -> DigestValidationWitness
  -> StorageWitness
  -> Either StorageError ()
verifyStorageWitness artifact digestWitness witness = do
  let program = systemsArtifactProgram artifact
      functionName = storageFunction witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (StorageFunctionMissing functionName)
    Just value -> Right value

  owner <- lookupValue functionName function (storageOwner witness) StorageOwnerMissing
  case systemsValueRole owner of
    OwnedBuffer _ -> pure ()
    other -> Left (StorageOwnerRoleMismatch functionName (storageOwner witness) other)

  result <- lookupValue functionName function (storageResult witness) StorageResultMissing
  case systemsValueRole result of
    RuntimeScalar "UploadId" -> pure ()
    other -> Left (StorageResultRoleMismatch functionName (storageResult witness) other)

  storeBlockValue <- lookupBlock functionName function (storageBlock witness)
  case systemsBlockTerminator storeBlockValue of
    TermStore
      { storeOwner = ownerValue
      , storeResult = resultValue
      , storeSite = site
      , storeSuccess = yes
      , storeFailure = no
      }
      | ownerValue == storageOwner witness
          && resultValue == storageResult witness
          && runtimeSiteKind site == StorageBoundary
          && yes == storageSuccess witness
          && no == storageFailure witness -> pure ()
    other -> Left (StorageTerminatorMismatch functionName (storageBlock witness) other)

  let stores =
        [ ()
        | blockValue <- Map.elems (systemsFunctionBlocks function)
        , TermStore { storeOwner = ownerValue } <- [systemsBlockTerminator blockValue]
        , ownerValue == storageOwner witness
        ]
  unless (length stores == 1) $
    Left (StorageMultiplicityMismatch functionName (storageOwner witness) (length stores))

  digestBlockValue <- lookupBlock functionName function (digestValidationBlock digestWitness)
  case systemsBlockTerminator digestBlockValue of
    TermRuntimeCheck
      { checkInputs = inputs
      , checkSite = site
      , checkSuccess = yes
      }
      | inputs == [digestValidationRecord digestWitness, digestValidationPayloadView digestWitness]
          && runtimeSiteKind site == DigestBoundary
          && yes == storageBlock witness -> pure ()
    other -> Left (StorageDigestPredecessorMismatch
      functionName
      (digestValidationBlock digestWitness)
      other)

  mapM_ (rejectRelease functionName function (storageOwner witness))
    [storageBlock witness, storageSuccess witness, storageFailure witness]

lookupValue
  :: Text
  -> SystemsFunction
  -> ValueId
  -> (Text -> ValueId -> StorageError)
  -> Either StorageError SystemsValue
lookupValue functionName function valueId missing =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (missing functionName valueId)
    Just value -> Right value

lookupBlock :: Text -> SystemsFunction -> BlockId -> Either StorageError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (StorageBlockMissing functionName blockId)
    Just value -> Right value

rejectRelease :: Text -> SystemsFunction -> ValueId -> BlockId -> Either StorageError ()
rejectRelease functionName function owner blockId = do
  blockValue <- lookupBlock functionName function blockId
  let releases =
        [ ()
        | operation <- systemsBlockOps blockValue
        , case operation of
            OpReleaseOwner released _ -> released == owner
            OpCleanupPartial released _ -> released == owner
            _ -> False
        ]
  unless (null releases) $
    Left (StorageExplicitReleaseAfterTransfer functionName blockId owner)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right