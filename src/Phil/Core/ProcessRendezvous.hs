{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessRendezvous
  ( ProcessRendezvousSide (..)
  , ProcessRendezvousRequest (..)
  , ProcessCommunicationAttempt (..)
  , ProcessRendezvousError (..)
  , checkProcessCommunication
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Process
  ( ActivationStatus (..)
  , ProcessKey
  , ProcessNetwork (..)
  , ProcessOccurrence (..)
  )
import Phil.Core.Protocol
  ( CheckedProtocolStep (..)
  , ProtocolActionRequest (..)
  , ProtocolCheckError
  , ProtocolContext
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
import Phil.Core.Syntax (Name, Session, Ty)

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

data ProcessRendezvousError
  = UnilateralRendezvousRejected ProcessKey ProtocolActionRequest
  | RendezvousUnknownProcess ProcessKey
  | RendezvousProcessNotActive ProcessKey ActivationStatus
  | RendezvousSameProcess ProcessKey
  | RendezvousMissingProtocolContext ProcessKey
  | RendezvousEndpointNotOwnedByProcess ProcessKey Name
  | RendezvousProtocolInstanceMismatch
      ProcessKey ProtocolInstanceRevision ProtocolInstanceRevision
  | RendezvousProtocolRoleMismatch
      ProcessKey ProtocolRoleKey ProtocolRoleKey
  | RendezvousProjectionSessionMismatch ProcessKey Session Session
  | RendezvousSameRole ProtocolRoleKey
  | RendezvousNonDualSessions ProcessKey ProcessKey
  | RendezvousMessageTypeMismatch Ty Ty
  | RendezvousProjectionError ProtocolFamilyError
  | RendezvousProtocolError ProcessKey ProtocolCheckError
  deriving (Eq, Show)

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
