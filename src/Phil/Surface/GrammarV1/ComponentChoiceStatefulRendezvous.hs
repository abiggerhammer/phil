{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02, non-normative. Source-checked select/offer followed by atomic
-- activation-derived endpoint occurrence ownership progression.
module Phil.Surface.GrammarV1.ComponentChoiceStatefulRendezvous
  ( GrammarV1StatefulChoiceError (..)
  , GrammarV1StatefulChoice (..)
  , grammarV1CheckStatefulSourceChoice
  , GrammarV1StatefulChoiceClientCloseError (..)
  , GrammarV1StatefulChoiceClientClose (..)
  , grammarV1CloseStatefulSourceChoiceClient
  ) where

import Data.Text (Text)
import Phil.Core.Process (ProcessKey, ProcessNetwork)
import Phil.Core.ProcessEndpointClosure
  ( ProcessEndpointClosureError, closeProcessEndpointState )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState (..)
  , ProcessRendezvousError
  , checkProcessCommunicationState
  )
import Phil.Core.Protocol (ProtocolRoleKey)
import Phil.Core.Protocol.Family (BinaryProtocolInstance (..))
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Name, Outcome)
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentSelectClose
  ( GrammarV1CheckedComponentSelectClose (..) )
import Phil.Surface.GrammarV1.ComponentChoiceRendezvous
  ( GrammarV1ChoiceRendezvous (..)
  , GrammarV1ChoiceRendezvousError
  , grammarV1CheckJointSourceChoice
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1ComponentDecl)

data GrammarV1StatefulChoiceError
  = GrammarV1StatefulChoiceSourceError GrammarV1ChoiceRendezvousError
  | GrammarV1StatefulChoiceOwnerError ProcessRendezvousError
  | GrammarV1StatefulChoiceContextDivergence
  deriving (Eq, Show)

data GrammarV1StatefulChoice = GrammarV1StatefulChoice
  { statefulChoiceSourceReplay :: GrammarV1ChoiceRendezvous
  , statefulChoiceSuccessor :: ProcessCommunicationState
  }
  deriving (Eq, Show)

-- | The supplied state must originate from communicationStateFromActivation
-- or a previously checked stateful Core transition. No root authority, payload
-- transfer, scheduler choice or nominal identity is invented here.
-- Source replay is a pure precheck. The production stateful joint transition
-- alone changes the owner index; comparison rejects contextual divergence.
grammarV1CheckStatefulSourceChoice
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
  -> ProcessCommunicationState
  -> Either GrammarV1StatefulChoiceError GrammarV1StatefulChoice
grammarV1CheckStatefulSourceChoice clientRoot clientSource offerRoot offerSource
    instanceValue clientRole offerRole clientProcess offerProcess offeredSuccessor
    peerLabel network state = do
  checked <- mapLeft GrammarV1StatefulChoiceSourceError $
    grammarV1CheckJointSourceChoice
      clientRoot clientSource offerRoot offerSource instanceValue
      clientRole offerRole clientProcess offerProcess offeredSuccessor
      peerLabel network (communicationProtocolContexts state)
  advanced <- mapLeft GrammarV1StatefulChoiceOwnerError $
    checkProcessCommunicationState instanceValue network state
      (jointChoiceRequest checked)
  if communicationProtocolContexts advanced == jointChoiceContexts checked
    then Right GrammarV1StatefulChoice
      { statefulChoiceSourceReplay = checked
      , statefulChoiceSuccessor = advanced
      }
    else Left GrammarV1StatefulChoiceContextDivergence


-- | The selected client's literal source 'close chosen' is actually executed
-- after a newly checked two-party stateful choice. The server's 'return unit'
-- arm is deliberately NOT interpreted as a peer endpoint close.
data GrammarV1StatefulChoiceClientCloseError
  = GrammarV1StatefulChoiceClientCloseSourceError GrammarV1StatefulChoiceError
  | GrammarV1StatefulChoiceClientCloseCoreError ProcessEndpointClosureError
  deriving (Eq, Show)

data GrammarV1StatefulChoiceClientClose = GrammarV1StatefulChoiceClientClose
  { statefulChoiceClientCloseSourceReplay :: GrammarV1StatefulChoice
  , statefulChoiceClientCloseEndpoint :: Name
  , statefulChoiceClientCloseSuccessor :: ProcessCommunicationState
  }
  deriving (Eq, Show)

-- | The caller supplies the initial activation-derived communication state,
-- checked instance, roles, process network, peer choice and terminal outcome.
-- Source checking resolves the exact selected successor / close operand.
-- The native Core stateful rendezvous and endpoint close both replay from
-- that input; no cached successor or source-derived nominal/root authority
-- is trusted. A failed close returns no progressed communication state.
grammarV1CloseStatefulSourceChoiceClient
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
  -> ProcessCommunicationState
  -> Outcome
  -> Either GrammarV1StatefulChoiceClientCloseError
       GrammarV1StatefulChoiceClientClose
grammarV1CloseStatefulSourceChoiceClient
    clientRoot clientSource offerRoot offerSource instanceValue
    clientRole offerRole clientProcess offerProcess offeredSuccessor peerLabel
    network initialState outcome = do
  progressed <- mapLeft GrammarV1StatefulChoiceClientCloseSourceError $
    grammarV1CheckStatefulSourceChoice
      clientRoot clientSource offerRoot offerSource instanceValue
      clientRole offerRole clientProcess offerProcess offeredSuccessor
      peerLabel network initialState
  let selected = jointChoiceSelectedSource (statefulChoiceSourceReplay progressed)
      clientSuccessor = grammarV1ResolvedBinderCoreName
        (checkedComponentSelectSuccessor selected)
  closed <- mapLeft GrammarV1StatefulChoiceClientCloseCoreError $
    closeProcessEndpointState network (statefulChoiceSuccessor progressed)
      clientProcess clientSuccessor (binaryProtocolInstanceRevision instanceValue)
      clientRole outcome
  pure GrammarV1StatefulChoiceClientClose
    { statefulChoiceClientCloseSourceReplay = progressed
    , statefulChoiceClientCloseEndpoint = clientSuccessor
    , statefulChoiceClientCloseSuccessor = closed
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
