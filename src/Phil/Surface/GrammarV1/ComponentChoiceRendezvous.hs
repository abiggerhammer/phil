{-# LANGUAGE OverloadedStrings #-}

-- Non-normative FSEM-02. Source-checked select/offer shapes are inputs to the
-- existing *joint* Core process transition. This is not a source evaluator,
-- architecture admission, owner-index transition, or restricted transfer.
module Phil.Surface.GrammarV1.ComponentChoiceRendezvous
  ( GrammarV1ChoiceRendezvousError (..)
  , GrammarV1ChoiceRendezvous (..)
  , grammarV1CheckJointSourceChoice
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Text (Text)
import Phil.Core.Process (ProcessKey, ProcessNetwork)
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationAttempt (..)
  , ProcessRendezvousError
  , ProcessRendezvousRequest (..)
  , ProcessRendezvousSide (..)
  , checkProcessCommunication
  )
import Phil.Core.Protocol
  ( CheckedProtocolStep (..)
  , ProtocolContext
  , ProtocolRoleKey
  )
import Phil.Core.Protocol.Family (BinaryProtocolInstance (..))
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Name)
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentOfferReplay
  ( GrammarV1ComponentOfferReplay (..)
  , GrammarV1ComponentOfferReplayError
  , grammarV1ReplayComponentOffer
  )
import Phil.Surface.GrammarV1.ComponentSelectClose
  ( GrammarV1CheckedComponentSelectClose (..)
  , GrammarV1ComponentSelectCloseError
  , grammarV1CheckedComponentSelectClose
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1ComponentDecl)

data GrammarV1ChoiceRendezvousError
  = GrammarV1JointChoiceUnsupportedSelectSource
  | GrammarV1JointChoiceSelectSourceError GrammarV1ComponentSelectCloseError
  | GrammarV1JointChoicePeerLabelMismatch Text Text
  | GrammarV1JointChoiceMissingOfferProcessContext ProcessKey
  | GrammarV1JointChoiceOfferSourceError GrammarV1ComponentOfferReplayError
  | GrammarV1JointChoiceCoreError ProcessRendezvousError
  | GrammarV1JointChoiceOfferReplayDivergence ProcessKey
  deriving (Eq, Show)

data GrammarV1ChoiceRendezvous = GrammarV1ChoiceRendezvous
  { jointChoiceSelectedSource :: GrammarV1CheckedComponentSelectClose
  , jointChoiceCheckedOffer :: GrammarV1ComponentOfferReplay
  , jointChoiceRequest :: ProcessRendezvousRequest
  , jointChoiceContexts :: Map ProcessKey ProtocolContext
  }
  deriving (Eq, Show)

-- | The client label comes from checked source; the peer's label is an explicit
-- external input and must agree. Both source-rooted endpoint names and the
-- selector successor come from the checked binder occurrences. The offered
-- successor, exact protocol instance, roles, process keys, active network and
-- current contexts are supplied by the caller, not guessed from spelling.
--
-- Offer replay is a pure precheck. Only checkProcessCommunication can produce
-- a successor map: the established Core joint checker verifies activation,
-- dual local heads, exact instance/role, two typed steps, and commits both
-- successors together. It does NOT advance the global owner occurrence index.
grammarV1CheckJointSourceChoice
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey
  -> ProtocolRoleKey
  -> ProcessKey
  -> ProcessKey
  -> Name
  -> Text
  -> ProcessNetwork
  -> Map ProcessKey ProtocolContext
  -> Either GrammarV1ChoiceRendezvousError GrammarV1ChoiceRendezvous
grammarV1CheckJointSourceChoice clientRoot clientSource offerRoot offerSource
    instanceValue clientRole offerRole clientProcess offerProcess offeredSuccessor
    peerLabel network contexts = do
  selected <- case grammarV1CheckedComponentSelectClose clientRoot clientSource of
    Nothing -> Left GrammarV1JointChoiceUnsupportedSelectSource
    Just checked -> mapLeft GrammarV1JointChoiceSelectSourceError checked
  let label = checkedComponentSelectLabel selected
  if label == peerLabel
    then Right ()
    else Left (GrammarV1JointChoicePeerLabelMismatch label peerLabel)
  offerContext <- maybe
    (Left (GrammarV1JointChoiceMissingOfferProcessContext offerProcess))
    Right (Map.lookup offerProcess contexts)
  offer <- mapLeft GrammarV1JointChoiceOfferSourceError $
    grammarV1ReplayComponentOffer offerRoot offerSource instanceValue
      offerRole label offeredSuccessor offerContext
  let revision = binaryProtocolInstanceRevision instanceValue
      clientEndpoint = grammarV1ResolvedBinderCoreName
        (checkedComponentSelectEndpoint selected)
      clientSuccessor = grammarV1ResolvedBinderCoreName
        (checkedComponentSelectSuccessor selected)
      offerEndpoint = grammarV1ResolvedBinderCoreName
        (replayedComponentOfferSourceEndpoint offer)
      clientSide = ProcessRendezvousSide
        { rendezvousProcess = clientProcess
        , rendezvousEndpoint = clientEndpoint
        , rendezvousSuccessor = clientSuccessor
        , rendezvousInstance = revision
        , rendezvousRole = clientRole
        }
      offerSide = ProcessRendezvousSide
        { rendezvousProcess = offerProcess
        , rendezvousEndpoint = offerEndpoint
        , rendezvousSuccessor = offeredSuccessor
        , rendezvousInstance = revision
        , rendezvousRole = offerRole
        }
      request = SelectOfferRendezvous clientSide offerSide label
  next <- mapLeft GrammarV1JointChoiceCoreError $
    checkProcessCommunication instanceValue network contexts
      (JointProcessRendezvous request)
  let offerReplayContext = checkedProtocolContext
        (replayedComponentOfferStep offer)
  if Map.lookup offerProcess next == Just offerReplayContext
    then Right GrammarV1ChoiceRendezvous
      { jointChoiceSelectedSource = selected
      , jointChoiceCheckedOffer = offer
      , jointChoiceRequest = request
      , jointChoiceContexts = next
      }
    else Left (GrammarV1JointChoiceOfferReplayDivergence offerProcess)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
