{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RejectedResponse
  ( RejectedResponseWitness (..)
  , RejectedResponseBundle (..)
  , RejectedResponseError (..)
  , phase0DigestMismatchReasonCode
  , phase0RejectedResponseWitness
  , phase0RejectedResponseBundle
  , verifyRejectedResponseBundle
  , verifyRejectedResponseWitness
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Systems.AcceptedResponse
import Phil.Systems.IR
import Phil.Systems.Verify (SystemsVerificationContext)

data RejectedResponseWitness = RejectedResponseWitness
  { rejectedResponseFunction :: Text
  , rejectedResponseDigestBlock :: BlockId
  , rejectedResponseBlock :: BlockId
  , rejectedResponseTransport :: ValueId
  , rejectedResponsePayloadOwner :: ValueId
  , rejectedResponseOperation :: Text
  , rejectedResponseReasonClass :: Text
  , rejectedResponseReasonCode :: Int
  , rejectedResponseOutcome :: Text
  }
  deriving (Eq, Show)

data RejectedResponseBundle = RejectedResponseBundle
  { rejectedResponseArtifact :: SystemsArtifact
  , rejectedResponseContext :: SystemsVerificationContext
  , rejectedResponseAcceptedBundle :: AcceptedResponseBundle
  , rejectedResponseWitness :: RejectedResponseWitness
  }
  deriving (Eq, Show)

data RejectedResponseError
  = RejectedResponseAcceptedError AcceptedResponseError
  | RejectedResponseFunctionMissing Text
  | RejectedResponseBlockMissing Text BlockId
  | RejectedResponseTransportMissing Text ValueId
  | RejectedResponseTransportRoleMismatch Text ValueId SystemsValueRole
  | RejectedResponsePayloadMissing Text ValueId
  | RejectedResponsePayloadRoleMismatch Text ValueId SystemsValueRole
  | RejectedResponseDigestPredecessorMismatch Text BlockId SystemsTerminator
  | RejectedResponseOperationMismatch Text BlockId [SystemsOp]
  | RejectedResponseTerminationMismatch Text BlockId SystemsTerminator
  | RejectedResponseReasonMappingMismatch Text Int
  deriving (Eq, Show)

-- Phase 0 exposes exactly one peer-visible reason after payload transfer.
-- Rich digest diagnostics are deliberately not protocol data.
phase0DigestMismatchReasonCode :: Int
phase0DigestMismatchReasonCode = 1

phase0RejectedResponseWitness :: RejectedResponseWitness
phase0RejectedResponseWitness = RejectedResponseWitness
  { rejectedResponseFunction = "UploadServer"
  , rejectedResponseDigestBlock = BlockId "server.digest"
  , rejectedResponseBlock = BlockId "server.digest_mismatch"
  , rejectedResponseTransport = ValueId "server.transport"
  , rejectedResponsePayloadOwner = ValueId "server.payload"
  , rejectedResponseOperation = "select rejected"
  , rejectedResponseReasonClass = "DigestMismatch"
  , rejectedResponseReasonCode = phase0DigestMismatchReasonCode
  , rejectedResponseOutcome = "failure"
  }

phase0RejectedResponseBundle :: Either RejectedResponseError RejectedResponseBundle
phase0RejectedResponseBundle = do
  acceptedBundle <- mapLeft RejectedResponseAcceptedError phase0AcceptedResponseBundle
  let bundle = RejectedResponseBundle
        { rejectedResponseArtifact = acceptedResponseArtifact acceptedBundle
        , rejectedResponseContext = acceptedResponseContext acceptedBundle
        , rejectedResponseAcceptedBundle = acceptedBundle
        , rejectedResponseWitness = phase0RejectedResponseWitness
        }
  verifyRejectedResponseBundle bundle
  pure bundle

verifyRejectedResponseBundle :: RejectedResponseBundle -> Either RejectedResponseError ()
verifyRejectedResponseBundle bundle = do
  mapLeft RejectedResponseAcceptedError $
    verifyAcceptedResponseBundle (rejectedResponseAcceptedBundle bundle)
  verifyRejectedResponseWitness
    (rejectedResponseArtifact bundle)
    (rejectedResponseWitness bundle)

verifyRejectedResponseWitness
  :: SystemsArtifact
  -> RejectedResponseWitness
  -> Either RejectedResponseError ()
verifyRejectedResponseWitness artifact witness = do
  let program = systemsArtifactProgram artifact
      functionName = rejectedResponseFunction witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (RejectedResponseFunctionMissing functionName)
    Just value -> Right value

  transport <- lookupValue functionName function
    (rejectedResponseTransport witness) RejectedResponseTransportMissing
  case systemsValueRole transport of
    TransportHandle -> pure ()
    other -> Left (RejectedResponseTransportRoleMismatch
      functionName (rejectedResponseTransport witness) other)

  payload <- lookupValue functionName function
    (rejectedResponsePayloadOwner witness) RejectedResponsePayloadMissing
  case systemsValueRole payload of
    OwnedBuffer _ -> pure ()
    other -> Left (RejectedResponsePayloadRoleMismatch
      functionName (rejectedResponsePayloadOwner witness) other)

  unless
    ( rejectedResponseReasonClass witness == "DigestMismatch"
    && rejectedResponseReasonCode witness == phase0DigestMismatchReasonCode
    ) $
    Left (RejectedResponseReasonMappingMismatch
      (rejectedResponseReasonClass witness)
      (rejectedResponseReasonCode witness))

  digestBlock <- lookupBlock functionName function (rejectedResponseDigestBlock witness)
  case systemsBlockTerminator digestBlock of
    TermRuntimeCheck
      { checkSite = site
      , checkFailure = failureBlock
      }
      | runtimeSiteKind site == DigestBoundary
          && failureBlock == rejectedResponseBlock witness -> pure ()
    other -> Left (RejectedResponseDigestPredecessorMismatch
      functionName (rejectedResponseDigestBlock witness) other)

  blockValue <- lookupBlock functionName function (rejectedResponseBlock witness)
  case systemsBlockOps blockValue of
    [ OpReleaseOwner owner _
      , OpRuntimeCall
          { runtimeCallName = name
          , runtimeCallInputs = inputs
          , runtimeCallOutputs = outputs
          , runtimeCallSite = site
          }
      ]
      | owner == rejectedResponsePayloadOwner witness
          && name == rejectedResponseOperation witness
          && inputs == [rejectedResponseTransport witness]
          && null outputs
          && site == Nothing -> pure ()
    operations -> Left (RejectedResponseOperationMismatch
      functionName (rejectedResponseBlock witness) operations)

  case systemsBlockTerminator blockValue of
    TermEnd outcome | outcome == rejectedResponseOutcome witness -> pure ()
    other -> Left (RejectedResponseTerminationMismatch
      functionName (rejectedResponseBlock witness) other)

lookupValue
  :: Text
  -> SystemsFunction
  -> ValueId
  -> (Text -> ValueId -> RejectedResponseError)
  -> Either RejectedResponseError SystemsValue
lookupValue functionName function valueId missing =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (missing functionName valueId)
    Just value -> Right value

lookupBlock :: Text -> SystemsFunction -> BlockId -> Either RejectedResponseError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (RejectedResponseBlockMissing functionName blockId)
    Just value -> Right value

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
