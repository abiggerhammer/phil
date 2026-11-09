{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02, non-normative. Source-checked select/offer followed by atomic
-- activation-derived endpoint occurrence ownership progression.
module Phil.Surface.GrammarV1.ComponentChoiceStatefulRendezvous
  ( GrammarV1StatefulChoiceError (..)
  , GrammarV1StatefulChoice (..)
  , grammarV1CheckStatefulSourceChoice
  ) where

import Data.Text (Text)
import Phil.Core.Process (ProcessKey, ProcessNetwork)
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState (..)
  , ProcessRendezvousError
  , checkProcessCommunicationState
  )
import Phil.Core.Protocol (ProtocolRoleKey)
import Phil.Core.Protocol.Family (BinaryProtocolInstance)
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Name)
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

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
