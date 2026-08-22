{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.AcceptedResponse
  ( AcceptedResponseWitness (..)
  , AcceptedResponseBundle (..)
  , AcceptedResponseError (..)
  , phase0AcceptedResponseWitness
  , phase0AcceptedResponseBundle
  , verifyAcceptedResponseBundle
  , verifyAcceptedResponseWitness
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Systems.IR
import Phil.Systems.Storage
import Phil.Systems.Verify (SystemsVerificationContext)

data AcceptedResponseWitness = AcceptedResponseWitness
  { acceptedResponseFunction :: Text
  , acceptedResponseBlock :: BlockId
  , acceptedResponseTransport :: ValueId
  , acceptedResponseUploadId :: ValueId
  , acceptedResponseOperation :: Text
  , acceptedResponseOutcome :: Text
  }
  deriving (Eq, Show)

data AcceptedResponseBundle = AcceptedResponseBundle
  { acceptedResponseArtifact :: SystemsArtifact
  , acceptedResponseContext :: SystemsVerificationContext
  , acceptedResponseStorageBundle :: StorageBundle
  , acceptedResponseWitness :: AcceptedResponseWitness
  }
  deriving (Eq, Show)

data AcceptedResponseError
  = AcceptedResponseStorageError StorageError
  | AcceptedResponseFunctionMissing Text
  | AcceptedResponseBlockMissing Text BlockId
  | AcceptedResponseTransportMissing Text ValueId
  | AcceptedResponseTransportRoleMismatch Text ValueId SystemsValueRole
  | AcceptedResponseUploadIdMissing Text ValueId
  | AcceptedResponseUploadIdRoleMismatch Text ValueId SystemsValueRole
  | AcceptedResponseOperationMismatch Text BlockId [SystemsOp]
  | AcceptedResponseTerminationMismatch Text BlockId SystemsTerminator
  | AcceptedResponseStoragePredecessorMismatch Text BlockId SystemsTerminator
  | AcceptedResponseUploadIdUseCountMismatch Text ValueId Int
  deriving (Eq, Show)

phase0AcceptedResponseWitness :: AcceptedResponseWitness
phase0AcceptedResponseWitness = AcceptedResponseWitness
  { acceptedResponseFunction = "UploadServer"
  , acceptedResponseBlock = BlockId "server.accepted"
  , acceptedResponseTransport = ValueId "server.transport"
  , acceptedResponseUploadId = ValueId "server.upload_id"
  , acceptedResponseOperation = "select accepted"
  , acceptedResponseOutcome = "success"
  }

phase0AcceptedResponseBundle :: Either AcceptedResponseError AcceptedResponseBundle
phase0AcceptedResponseBundle = do
  storageBundle <- mapLeft AcceptedResponseStorageError phase0StorageBundle
  let bundle = AcceptedResponseBundle
        { acceptedResponseArtifact = storageArtifact storageBundle
        , acceptedResponseContext = storageContext storageBundle
        , acceptedResponseStorageBundle = storageBundle
        , acceptedResponseWitness = phase0AcceptedResponseWitness
        }
  verifyAcceptedResponseBundle bundle
  pure bundle

verifyAcceptedResponseBundle :: AcceptedResponseBundle -> Either AcceptedResponseError ()
verifyAcceptedResponseBundle bundle = do
  mapLeft AcceptedResponseStorageError $
    verifyStorageBundle (acceptedResponseStorageBundle bundle)
  verifyAcceptedResponseWitness
    (acceptedResponseArtifact bundle)
    (storageWitness (acceptedResponseStorageBundle bundle))
    (acceptedResponseWitness bundle)

verifyAcceptedResponseWitness
  :: SystemsArtifact
  -> StorageWitness
  -> AcceptedResponseWitness
  -> Either AcceptedResponseError ()
verifyAcceptedResponseWitness artifact storeWitness witness = do
  let program = systemsArtifactProgram artifact
      functionName = acceptedResponseFunction witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (AcceptedResponseFunctionMissing functionName)
    Just value -> Right value

  transport <- lookupValue functionName function
    (acceptedResponseTransport witness) AcceptedResponseTransportMissing
  case systemsValueRole transport of
    TransportHandle -> pure ()
    other -> Left (AcceptedResponseTransportRoleMismatch
      functionName (acceptedResponseTransport witness) other)

  uploadId <- lookupValue functionName function
    (acceptedResponseUploadId witness) AcceptedResponseUploadIdMissing
  case systemsValueRole uploadId of
    RuntimeScalar "UploadId" -> pure ()
    other -> Left (AcceptedResponseUploadIdRoleMismatch
      functionName (acceptedResponseUploadId witness) other)

  blockValue <- lookupBlock functionName function (acceptedResponseBlock witness)
  let matching =
        [ operation
        | operation@OpRuntimeCall
            { runtimeCallName = name
            , runtimeCallInputs = inputs
            , runtimeCallOutputs = outputs
            , runtimeCallSite = site
            } <- systemsBlockOps blockValue
        , name == acceptedResponseOperation witness
        , inputs == [acceptedResponseTransport witness, acceptedResponseUploadId witness]
        , null outputs
        , site == Nothing
        ]
  unless (matching == systemsBlockOps blockValue && length matching == 1) $
    Left (AcceptedResponseOperationMismatch
      functionName (acceptedResponseBlock witness) (systemsBlockOps blockValue))

  case systemsBlockTerminator blockValue of
    TermEnd outcome | outcome == acceptedResponseOutcome witness -> pure ()
    other -> Left (AcceptedResponseTerminationMismatch
      functionName (acceptedResponseBlock witness) other)

  storeBlockValue <- lookupBlock functionName function (storageBlock storeWitness)
  case systemsBlockTerminator storeBlockValue of
    term@TermStore { storeResult = resultValue, storeSuccess = yes }
      | resultValue == acceptedResponseUploadId witness
          && yes == acceptedResponseBlock witness -> pure ()
    other -> Left (AcceptedResponseStoragePredecessorMismatch
      functionName (storageBlock storeWitness) other)

  let uploadIdUses =
        [ ()
        | candidateBlock <- Map.elems (systemsFunctionBlocks function)
        , operation <- systemsBlockOps candidateBlock
        , acceptedResponseUploadId witness `elem` operationInputs operation
        ]
  unless (length uploadIdUses == 1) $
    Left (AcceptedResponseUploadIdUseCountMismatch
      functionName (acceptedResponseUploadId witness) (length uploadIdUses))

lookupValue
  :: Text
  -> SystemsFunction
  -> ValueId
  -> (Text -> ValueId -> AcceptedResponseError)
  -> Either AcceptedResponseError SystemsValue
lookupValue functionName function valueId missing =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (missing functionName valueId)
    Just value -> Right value

lookupBlock :: Text -> SystemsFunction -> BlockId -> Either AcceptedResponseError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (AcceptedResponseBlockMissing functionName blockId)
    Just value -> Right value

operationInputs :: SystemsOp -> [ValueId]
operationInputs operation = case operation of
  OpReceiveFrame pending frame transport _ _ -> [pending, frame, transport]
  OpBorrowView view owner _ -> [view, owner]
  OpCommitIngress pending transport _ -> [pending, transport]
  OpDestroyPending pending owner _ -> [pending, owner]
  OpReleaseOwner owner _ -> [owner]
  OpCleanupPartial owner _ -> [owner]
  OpRuntimeCall _ inputs _ _ _ -> inputs
  OpCopy source target _ -> [source, target]
  OpEraseFact {} -> []
  OpDiagnostic {} -> []
  OpScalarLiteral output _ -> [output]
  OpTraceEvent _ -> []

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
