{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessRendezvous
  ( ProcessRendezvousSide (..)
  , ProcessRendezvousRequest (..)
  , ProcessCommunicationAttempt (..)
  , RestrictedMessageTransfer (..)
  , ProcessCommunicationState (..)
  , ProcessRendezvousError (..)
  , communicationStateFromActivation
  , checkProcessCommunication
  , checkRestrictedProcessRendezvous
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Context
  ( CheckError
  , ResourceContext
  , consumeAffine
  , consumeLinear
  , insertBinding
  )
import Phil.Core.Process
  ( ActivationStatus (..)
  , ProcessKey
  , ProcessNetwork (..)
  , ProcessOccurrence (..)
  )
import Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey
  , ProcessActivationState (..)
  , RestrictedOwnerIndex
  )
import Phil.Core.Protocol
  ( CheckedProtocolStep (..)
  , ProtocolActionRequest (..)
  , ProtocolCheckError
  , ProtocolContext (..)
  , ProtocolEndpointBinding (..)
  , ProtocolInstanceRevision
  , ProtocolRoleKey
  , checkProtocolAction
  , lookupProtocolEndpoint
  )
import Phil.Core.Protocol.Family
  ( BinaryProtocolInstance (..)
  , ProtocolFamilyError
  , ProtocolProjectionEvidence (..)
  , projectProtocolRole
  )
import Phil.Core.Session
  ( MessageSpec (..)
  , SessionStep (..)
  , dualSession
  )
import Phil.Core.Syntax (Mode (..), Name, Session, Ty)

data ProcessRendezvousSide = ProcessRendezvousSide
  { rendezvousProcess :: ProcessKey
  , rendezvousEndpoint :: Name
  , rendezvousSuccessor :: Name
  , rendezvousInstance :: ProtocolInstanceRevision
  , rendezvousRole :: ProtocolRoleKey
  }
  deriving (Eq, Show)

data ProcessRendezvousRequest
  = SendReceiveRendezvous
      ProcessRendezvousSide
      ProcessRendezvousSide
  | SelectOfferRendezvous
      ProcessRendezvousSide
      ProcessRendezvousSide
      Text
  deriving (Eq, Show)

data ProcessCommunicationAttempt
  = JointProcessRendezvous ProcessRendezvousRequest
  | UnilateralProcessAction ProcessKey ProtocolActionRequest
  deriving (Eq, Show)

-- | Exact restricted semantic occurrence transferred by one synchronous
-- send/receive. The occurrence identity is retained from process activation;
-- local names may change as ownership moves between process contexts.
data RestrictedMessageTransfer = RestrictedMessageTransfer
  { restrictedMessageOccurrence :: ActivationOccurrenceKey
  , restrictedMessageSenderName :: Name
  , restrictedMessageReceiverName :: Name
  , restrictedMessageMode :: Mode
  , restrictedMessageType :: Ty
  }
  deriving (Eq, Show)

-- | Live process communication state: protocol/resource contexts plus the exact
-- global owner index established at activation and subsequently maintained by
-- ownership-moving rendezvous transitions.
data ProcessCommunicationState = ProcessCommunicationState
  { communicationProtocolContexts :: Map.Map ProcessKey ProtocolContext
  , communicationRestrictedOwners :: RestrictedOwnerIndex
  }
  deriving (Eq, Show)

data ProcessRendezvousError
  = UnilateralRendezvousRejected ProcessKey ProtocolActionRequest
  | RendezvousUnknownProcess ProcessKey
  | RendezvousProcessNotActive ProcessKey ActivationStatus
  | RendezvousSameProcess ProcessKey
  | RendezvousMissingProtocolContext ProcessKey
  | RendezvousUnexpectedProtocolContext ProcessKey
  | RendezvousActivationResourceMismatch
      ProcessKey ResourceContext ResourceContext
  | RendezvousEndpointNotOwnedByProcess ProcessKey Name
  | RendezvousProtocolInstanceMismatch
      ProcessKey ProtocolInstanceRevision ProtocolInstanceRevision
  | RendezvousProtocolRoleMismatch
      ProcessKey ProtocolRoleKey ProtocolRoleKey
  | RendezvousProjectionSessionMismatch ProcessKey Session Session
  | RendezvousSameRole ProtocolRoleKey
  | RendezvousNonDualSessions ProcessKey ProcessKey
  | RendezvousMessageTypeMismatch Ty Ty
  | RestrictedMessageRequiresSendReceive
  | RestrictedMessageModeNotRestricted Mode
  | RestrictedMessageOwnerUnknown ActivationOccurrenceKey
  | RestrictedMessageOwnerMismatch
      ActivationOccurrenceKey
      ProcessKey Name
      ProcessKey Name
  | RestrictedMessageMissingPayload ProcessKey
  | RestrictedMessageReceiverBinderMismatch Name Name
  | RestrictedMessageTransferTypeMismatch Ty Ty
  | RestrictedMessageSenderResourceError ProcessKey CheckError
  | RestrictedMessageReceiverResourceError ProcessKey CheckError
  | RendezvousProjectionError ProtocolFamilyError
  | RendezvousProtocolError ProcessKey ProtocolCheckError
  deriving (Eq, Show)

-- | Join the exact owner partition produced by CONC-003 to protocol metadata.
-- The protocol contexts must cover exactly the activated process population and
-- must carry byte-for-byte equal ResourceContexts; metadata may add endpoint
-- identity, but it may not rewrite the activation resource state.
communicationStateFromActivation
  :: ProcessActivationState
  -> Map.Map ProcessKey ProtocolContext
  -> Either ProcessRendezvousError ProcessCommunicationState
communicationStateFromActivation activationState protocolContexts = do
  mapM_ requireAgreement (Map.toList activationContexts)
  case Set.lookupMin extraProtocolContexts of
    Just processKey -> Left (RendezvousUnexpectedProtocolContext processKey)
    Nothing -> Right ProcessCommunicationState
      { communicationProtocolContexts = protocolContexts
      , communicationRestrictedOwners = activationRestrictedOwners activationState
      }
  where
    activationContexts = activationProcessContexts activationState
    extraProtocolContexts =
      Map.keysSet protocolContexts `Set.difference` Map.keysSet activationContexts

    requireAgreement (processKey, expectedResources) = do
      protocolContext <- requireContext protocolContexts processKey
      let actualResources = protocolResources protocolContext
      if actualResources == expectedResources
        then Right ()
        else Left (RendezvousActivationResourceMismatch
          processKey expectedResources actualResources)

-- | Check one source-semantic process communication attempt. A legal internal
-- communication is one joint transition: both exact endpoint actions are
-- checked against one binary protocol instance and either both successor
-- contexts are returned or no process context advances.
checkProcessCommunication
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> Map.Map ProcessKey ProtocolContext
  -> ProcessCommunicationAttempt
  -> Either ProcessRendezvousError (Map.Map ProcessKey ProtocolContext)
checkProcessCommunication instanceValue network contexts attempt =
  case attempt of
    UnilateralProcessAction processKey request ->
      Left (UnilateralRendezvousRejected processKey request)
    JointProcessRendezvous request ->
      checkJointRendezvous instanceValue network contexts request

-- | CONC-005: perform one exact send/receive rendezvous and move one exact
-- affine/linear payload occurrence sender -> receiver in the same pure checked
-- transition. Endpoint progression, resource movement, and owner-index update
-- all succeed together or no successor state is returned.
checkRestrictedProcessRendezvous
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> ProcessRendezvousRequest
  -> RestrictedMessageTransfer
  -> Either ProcessRendezvousError ProcessCommunicationState
checkRestrictedProcessRendezvous instanceValue network state request transfer =
  case request of
    SelectOfferRendezvous _ _ _ -> Left RestrictedMessageRequiresSendReceive
    SendReceiveRendezvous sender receiver -> do
      ensureRestrictedMode (restrictedMessageMode transfer)
      ensureExactSenderOwner
        (communicationRestrictedOwners state)
        sender
        transfer
      let contexts = communicationProtocolContexts state
      senderBefore <- requireContext contexts (rendezvousProcess sender)
      receiverBefore <- requireContext contexts (rendezvousProcess receiver)
      let (senderAction, receiverAction) = protocolRequests request
      senderStep <- mapLeft (RendezvousProtocolError (rendezvousProcess sender)) $
        checkProtocolAction senderAction senderBefore
      receiverStep <- mapLeft (RendezvousProtocolError (rendezvousProcess receiver)) $
        checkProtocolAction receiverAction receiverBefore
      checkTransferMessageContract sender receiver senderStep receiverStep transfer
      progressed <- checkJointRendezvous instanceValue network contexts request
      senderAfter <- requireContext progressed (rendezvousProcess sender)
      receiverAfter <- requireContext progressed (rendezvousProcess receiver)
      (actualPayloadType, senderResources) <- mapLeft
        (RestrictedMessageSenderResourceError (rendezvousProcess sender)) $
        consumeRestricted
          (restrictedMessageMode transfer)
          (restrictedMessageSenderName transfer)
          (protocolResources senderAfter)
      requireEqual RestrictedMessageTransferTypeMismatch
        (restrictedMessageType transfer) actualPayloadType
      receiverResources <- mapLeft
        (RestrictedMessageReceiverResourceError (rendezvousProcess receiver)) $
        insertBinding
          (restrictedMessageMode transfer)
          (restrictedMessageReceiverName transfer)
          (restrictedMessageType transfer)
          (protocolResources receiverAfter)
      let senderUpdated = senderAfter { protocolResources = senderResources }
          receiverUpdated = receiverAfter { protocolResources = receiverResources }
          contextsUpdated =
            Map.insert (rendezvousProcess receiver) receiverUpdated $
              Map.insert (rendezvousProcess sender) senderUpdated progressed
          ownersUpdated = Map.insert
            (restrictedMessageOccurrence transfer)
            (rendezvousProcess receiver, restrictedMessageReceiverName transfer)
            (communicationRestrictedOwners state)
      pure ProcessCommunicationState
        { communicationProtocolContexts = contextsUpdated
        , communicationRestrictedOwners = ownersUpdated
        }

checkJointRendezvous
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> Map.Map ProcessKey ProtocolContext
  -> ProcessRendezvousRequest
  -> Either ProcessRendezvousError (Map.Map ProcessKey ProtocolContext)
checkJointRendezvous instanceValue network contexts request = do
  let left = requestLeft request
      right = requestRight request
  if rendezvousProcess left == rendezvousProcess right
    then Left (RendezvousSameProcess (rendezvousProcess left))
    else Right ()
  requireActive network (rendezvousProcess left)
  requireActive network (rendezvousProcess right)
  leftContext <- requireContext contexts (rendezvousProcess left)
  rightContext <- requireContext contexts (rendezvousProcess right)
  leftBinding <- validateSide instanceValue left leftContext
  rightBinding <- validateSide instanceValue right rightContext
  if rendezvousRole left == rendezvousRole right
    then Left (RendezvousSameRole (rendezvousRole left))
    else Right ()
  if protocolEndpointSession rightBinding
      == dualSession (protocolEndpointSession leftBinding)
    then Right ()
    else Left (RendezvousNonDualSessions
      (rendezvousProcess left) (rendezvousProcess right))
  let (leftAction, rightAction) = protocolRequests request
  leftStep <- mapLeft (RendezvousProtocolError (rendezvousProcess left)) $
    checkProtocolAction leftAction leftContext
  rightStep <- mapLeft (RendezvousProtocolError (rendezvousProcess right)) $
    checkProtocolAction rightAction rightContext
  checkJointMessage leftStep rightStep request
  pure $
    Map.insert (rendezvousProcess right) (checkedProtocolContext rightStep) $
      Map.insert (rendezvousProcess left) (checkedProtocolContext leftStep) contexts

validateSide
  :: BinaryProtocolInstance
  -> ProcessRendezvousSide
  -> ProtocolContext
  -> Either ProcessRendezvousError ProtocolEndpointBinding
validateSide instanceValue side context = do
  let processKey = rendezvousProcess side
      exactInstance = binaryProtocolInstanceRevision instanceValue
  requireEqual
    (RendezvousProtocolInstanceMismatch processKey)
    exactInstance
    (rendezvousInstance side)
  binding <- maybe
    (Left (RendezvousEndpointNotOwnedByProcess processKey (rendezvousEndpoint side)))
    Right
    (lookupProtocolEndpoint (rendezvousEndpoint side) context)
  requireEqual
    (RendezvousProtocolInstanceMismatch processKey)
    exactInstance
    (protocolEndpointInstance binding)
  requireEqual
    (RendezvousProtocolRoleMismatch processKey)
    (rendezvousRole side)
    (protocolEndpointRole binding)
  projection <- mapLeft RendezvousProjectionError $
    projectProtocolRole instanceValue (rendezvousRole side)
  requireEqual
    (RendezvousProjectionSessionMismatch processKey)
    (protocolProjectionSession projection)
    (protocolEndpointSession binding)
  pure binding

requireActive :: ProcessNetwork -> ProcessKey -> Either ProcessRendezvousError ()
requireActive network processKey =
  case Map.lookup processKey (processNetworkPopulation network) of
    Nothing -> Left (RendezvousUnknownProcess processKey)
    Just occurrence ->
      case processOccurrenceActivation occurrence of
        Active -> Right ()
        status -> Left (RendezvousProcessNotActive processKey status)

requireContext
  :: Map.Map ProcessKey ProtocolContext
  -> ProcessKey
  -> Either ProcessRendezvousError ProtocolContext
requireContext contexts processKey =
  maybe
    (Left (RendezvousMissingProtocolContext processKey))
    Right
    (Map.lookup processKey contexts)

protocolRequests
  :: ProcessRendezvousRequest
  -> (ProtocolActionRequest, ProtocolActionRequest)
protocolRequests request =
  case request of
    SendReceiveRendezvous sender receiver ->
      ( ProtocolSendRequest
          (rendezvousEndpoint sender)
          (rendezvousSuccessor sender)
          (rendezvousInstance sender)
          (rendezvousRole sender)
      , ProtocolReceiveRequest
          (rendezvousEndpoint receiver)
          (rendezvousSuccessor receiver)
          (rendezvousInstance receiver)
          (rendezvousRole receiver)
      )
    SelectOfferRendezvous selector offerer label ->
      ( ProtocolSelectRequest
          (rendezvousEndpoint selector)
          (rendezvousSuccessor selector)
          (rendezvousInstance selector)
          (rendezvousRole selector)
          label
      , ProtocolOfferRequest
          (rendezvousEndpoint offerer)
          (rendezvousSuccessor offerer)
          (rendezvousInstance offerer)
          (rendezvousRole offerer)
          label
      )

checkJointMessage
  :: CheckedProtocolStep
  -> CheckedProtocolStep
  -> ProcessRendezvousRequest
  -> Either ProcessRendezvousError ()
checkJointMessage leftStep rightStep request =
  case request of
    SelectOfferRendezvous _ _ _ -> Right ()
    SendReceiveRendezvous _ _ ->
      case ( stepMessage (checkedProtocolSessionStep leftStep)
           , stepMessage (checkedProtocolSessionStep rightStep)
           ) of
        (Just leftMessage, Just rightMessage) ->
          requireEqual RendezvousMessageTypeMismatch
            (messageType leftMessage)
            (messageType rightMessage)
        _ -> Right ()

checkTransferMessageContract
  :: ProcessRendezvousSide
  -> ProcessRendezvousSide
  -> CheckedProtocolStep
  -> CheckedProtocolStep
  -> RestrictedMessageTransfer
  -> Either ProcessRendezvousError ()
checkTransferMessageContract sender receiver senderStep receiverStep transfer = do
  senderMessage <- maybe
    (Left (RestrictedMessageMissingPayload (rendezvousProcess sender)))
    Right
    (stepMessage (checkedProtocolSessionStep senderStep))
  receiverMessage <- maybe
    (Left (RestrictedMessageMissingPayload (rendezvousProcess receiver)))
    Right
    (stepMessage (checkedProtocolSessionStep receiverStep))
  requireEqual RestrictedMessageTransferTypeMismatch
    (restrictedMessageType transfer) (messageType senderMessage)
  requireEqual RestrictedMessageTransferTypeMismatch
    (restrictedMessageType transfer) (messageType receiverMessage)
  requireEqual RestrictedMessageReceiverBinderMismatch
    (messageBinder receiverMessage) (restrictedMessageReceiverName transfer)

ensureRestrictedMode :: Mode -> Either ProcessRendezvousError ()
ensureRestrictedMode mode =
  case mode of
    Unrestricted -> Left (RestrictedMessageModeNotRestricted mode)
    Affine -> Right ()
    Linear -> Right ()

ensureExactSenderOwner
  :: RestrictedOwnerIndex
  -> ProcessRendezvousSide
  -> RestrictedMessageTransfer
  -> Either ProcessRendezvousError ()
ensureExactSenderOwner owners sender transfer =
  case Map.lookup (restrictedMessageOccurrence transfer) owners of
    Nothing -> Left (RestrictedMessageOwnerUnknown
      (restrictedMessageOccurrence transfer))
    Just (actualProcess, actualName)
      | actualProcess == expectedProcess && actualName == expectedName -> Right ()
      | otherwise -> Left (RestrictedMessageOwnerMismatch
          (restrictedMessageOccurrence transfer)
          expectedProcess expectedName
          actualProcess actualName)
  where
    expectedProcess = rendezvousProcess sender
    expectedName = restrictedMessageSenderName transfer

consumeRestricted
  :: Mode
  -> Name
  -> ResourceContext
  -> Either CheckError (Ty, ResourceContext)
consumeRestricted mode name context =
  case mode of
    Affine -> consumeAffine name context
    Linear -> consumeLinear name context
    Unrestricted -> error "consumeRestricted called with Unrestricted after validation"

requestLeft :: ProcessRendezvousRequest -> ProcessRendezvousSide
requestLeft request = case request of
  SendReceiveRendezvous left _ -> left
  SelectOfferRendezvous left _ _ -> left

requestRight :: ProcessRendezvousRequest -> ProcessRendezvousSide
requestRight request = case request of
  SendReceiveRendezvous _ right -> right
  SelectOfferRendezvous _ right _ -> right

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual constructor expected actual
  | expected == actual = Right ()
  | otherwise = Left (constructor expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
