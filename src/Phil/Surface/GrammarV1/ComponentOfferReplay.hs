{-# LANGUAGE OverloadedStrings #-}

-- Non-normative FSEM-02: selected return-unit source offer arm to one
-- production Core local offer step. Selection and successor name are inputs;
-- this is neither network rendezvous nor execution of general arm bodies.
module Phil.Surface.GrammarV1.ComponentOfferReplay
  ( GrammarV1ComponentOfferReplay (..)
  , GrammarV1ComponentOfferReplayError (..)
  , grammarV1ReplayComponentOffer
  ) where

import Data.Text (Text)
import Phil.Core.Protocol
  ( CheckedProtocolStep
  , ProtocolActionRequest (..)
  , ProtocolCheckError (..)
  , ProtocolContext
  , ProtocolEndpointBinding (..)
  , checkProtocolAction
  , lookupProtocolEndpoint
  )
import Phil.Core.Protocol.Family
  ( BinaryProtocolInstance
  , ProtocolFamilyError
  , ProtocolProjectionEvidence (..)
  , projectProtocolRole
  )
import Phil.Core.Protocol (ProtocolRoleKey)
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Name, Session)
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentOfferCoverage
  ( GrammarV1CheckedComponentOfferCoverage (..)
  , GrammarV1ComponentOfferCoverageError
  , grammarV1CheckedComponentOfferCoverage
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1ComponentDecl)

data GrammarV1ComponentOfferReplayError
  = GrammarV1OfferReplayUnsupportedSource
  | GrammarV1OfferReplayCoverageError GrammarV1ComponentOfferCoverageError
  | GrammarV1OfferReplayProjectionError ProtocolFamilyError
  | GrammarV1OfferReplayUnlistedLabel Text
  | GrammarV1OfferReplayWrongLiveHead Session Session
  | GrammarV1OfferReplayProtocolError ProtocolCheckError
  deriving (Eq, Show)

data GrammarV1ComponentOfferReplay = GrammarV1ComponentOfferReplay
  { replayedComponentOfferLabel :: Text
  , replayedComponentOfferSourceEndpoint :: GrammarV1ResolvedBinder
  , replayedComponentOfferProjection :: ProtocolProjectionEvidence
  , replayedComponentOfferStep :: CheckedProtocolStep
  }
  deriving (Eq, Show)

-- | The source body is already checked to consist solely of literal
-- return-unit arms with exact label coverage. A chosen label is a distinct,
-- EXTERNAL input, not a scheduler/rendezvous fact inferred from source.
-- The role comes from a caller-supplied, already instantiated binary protocol;
-- projectProtocolRole checks its membership and exact projection identity.
-- The exact source-rooted endpoint occurrence must exist in live Core state
-- with precisely the projected session head. Core then independently checks
-- instance/role, freshness, typed successor and predecessor consumption.
-- This adapter does not evaluate return-unit as an endpoint close.
grammarV1ReplayComponentOffer
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey
  -> Text
  -> Name
  -> ProtocolContext
  -> Either GrammarV1ComponentOfferReplayError GrammarV1ComponentOfferReplay
grammarV1ReplayComponentOffer root component instanceValue role selectedLabel successor context = do
  projection <- mapLeft GrammarV1OfferReplayProjectionError $
    projectProtocolRole instanceValue role
  coverage <- case grammarV1CheckedComponentOfferCoverage
      root component (protocolProjectionSession projection) of
    Nothing -> Left GrammarV1OfferReplayUnsupportedSource
    Just result -> mapLeft GrammarV1OfferReplayCoverageError result
  if elem selectedLabel (checkedComponentOfferLabels coverage)
    then Right ()
    else Left (GrammarV1OfferReplayUnlistedLabel selectedLabel)
  let sourceEndpoint = checkedComponentOfferEndpoint coverage
      endpoint = grammarV1ResolvedBinderCoreName sourceEndpoint
  live <- maybe
    (Left (GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown endpoint)))
    Right (lookupProtocolEndpoint endpoint context)
  let projectedHead = protocolProjectionSession projection
      liveHead = protocolEndpointSession live
  if projectedHead == liveHead
    then Right ()
    else Left (GrammarV1OfferReplayWrongLiveHead projectedHead liveHead)
  stepped <- mapLeft GrammarV1OfferReplayProtocolError $
    checkProtocolAction
      (ProtocolOfferRequest endpoint successor
        (protocolProjectionInstance projection)
        (protocolProjectionRole projection) selectedLabel)
      context
  Right GrammarV1ComponentOfferReplay
    { replayedComponentOfferLabel = selectedLabel
    , replayedComponentOfferSourceEndpoint = sourceEndpoint
    , replayedComponentOfferProjection = projection
    , replayedComponentOfferStep = stepped
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
