{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ConcurrencyRendezvousCertification
  ( CertifiedRendezvousActivation
  , certifiedRendezvousActivationNetwork
  , certifiedRendezvousActivationState
  , certifiedRendezvousParticipantClassification
  , CertifiedRendezvousProtocol
  , certifiedRendezvousProtocolInstance
  , certifiedRendezvousPrimaryRole
  , certifiedRendezvousPeerRole
  , RendezvousMessageEvidence (..)
  , rendezvousMessageEvidenceFromArgument
  , RendezvousEndpointKernelFacts (..)
  , RendezvousParticipantKernelFacts (..)
  , RendezvousMessageCoarseKernelFacts (..)
  , CertifiedRendezvousCausality
  , certifiedRendezvousSenderProcess
  , certifiedRendezvousReceiverProcess
  , certifiedRendezvousEventKind
  , CertifiedRendezvousResult
  , certifiedRendezvousState
  , certifiedRendezvousCausality
  , ConcurrencyRendezvousCertificationError (..)
  , certifyRendezvousActivation
  , certifyRendezvousProtocol
  , verifyRendezvousEndpointKernelFacts
  , verifyRendezvousParticipantKernelFacts
  , verifyRendezvousMessageCoarseKernelFacts
  , verifyExactInternalRendezvousKernelFacts
  , certifyProcessRendezvous
  , certifyRestrictedProcessRendezvous
  ) where

import qualified ConcurrencyRendezvousKernel as Kernel
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.ConcurrencyActivationCertification
  ( ConcurrencyActivationCertificationError
  , ConcurrencyActivationCertificationResult
  , certifiedActivationNetwork
  , certifiedActivationState
  , certifiedParticipantClassification
  , certifyConcurrencyActivation
  )
import Phil.Core.Generic
  ( GenericInstantiationPolicy
  , GenericRequirement
  , GenericRequirementDisposition
  )
import Phil.Core.Process (ProcessKey, ProcessNetwork)
import Phil.Core.ProcessActivation
  ( ProcessActivationContract
  , ProcessActivationState
  )
import Phil.Core.ProcessCausality (ProcessEventKind (..))
import Phil.Core.ProcessParticipants
  ( CheckedParticipant (..)
  , ParticipantClassification (..)
  , ParticipantDeclaration
  , ProtocolRoleOccurrence (..)
  )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState (..)
  , ProcessRendezvousError
  , ProcessRendezvousRequest (..)
  , ProcessRendezvousSide (..)
  , RestrictedMessageTransfer (..)
  , checkProcessCommunication
  , checkRestrictedProcessRendezvous
  , communicationStateFromActivation
  , ProcessCommunicationAttempt (JointProcessRendezvous)
  )
import Phil.Core.Protocol
  ( CheckedProtocolStep (..)
  , ProtocolCheckError
  , ProtocolContext
  , ProtocolEndpointBinding (..)
  , ProtocolActionRequest (..)
  , ProtocolInstanceRevision (..)
  , ProtocolRoleKey
  , checkProtocolAction
  , lookupProtocolEndpoint
  )
import Phil.Core.Protocol.Family
  ( BinaryProtocolFamily (..)
  , BinaryProtocolInstance
  , ProtocolFamilyError
  , ProtocolMessageArgument (..)
  , ProtocolProjectionEvidence (..)
  , instantiateBinaryProtocol
  , intrinsicBoundaryMessageType
  , projectProtocolRole
  )
import Phil.Core.Protocol.MessageAdmissibility
  ( BoundaryMessageContract
  , BoundaryMessageError
  , checkBoundaryMessageContract
  )
import Phil.Core.Session
  ( MessageSpec (..)
  , SessionStep (..)
  , dualSession
  )
import Phil.Core.Static
  ( ArchitectureInstanceGraph
  , SemanticForm
  )
import Phil.Core.Syntax (Session, Ty)

-- | Opaque production witness: callers can inspect the already-certified
-- activation result, but cannot manufacture one without rerunning #687's
-- native-first + exact-kernel predecessor.
newtype CertifiedRendezvousActivation = CertifiedRendezvousActivation
  { unCertifiedRendezvousActivation :: ConcurrencyActivationCertificationResult
  }
  deriving (Eq, Show)

certifiedRendezvousActivationNetwork :: CertifiedRendezvousActivation -> ProcessNetwork
certifiedRendezvousActivationNetwork =
  certifiedActivationNetwork . unCertifiedRendezvousActivation

certifiedRendezvousActivationState :: CertifiedRendezvousActivation -> ProcessActivationState
certifiedRendezvousActivationState =
  certifiedActivationState . unCertifiedRendezvousActivation

certifiedRendezvousParticipantClassification
  :: CertifiedRendezvousActivation
  -> ParticipantClassification
certifiedRendezvousParticipantClassification =
  certifiedParticipantClassification . unCertifiedRendezvousActivation

-- | Opaque exact binary-protocol witness.  Unlike BinaryProtocolInstance's
-- compact runtime representation, this retains the source family's primary/peer
-- orientation and exact initial dual projections required by the Certified
-- rendezvous theorem.
data CertifiedRendezvousProtocol = CertifiedRendezvousProtocol
  { certifiedRendezvousProtocolInstance :: BinaryProtocolInstance
  , certifiedRendezvousPrimaryRole :: ProtocolRoleKey
  , certifiedRendezvousPeerRole :: ProtocolRoleKey
  , certifiedRendezvousPrimarySession :: Session
  , certifiedRendezvousPeerSession :: Session
  , certifiedRendezvousProtocolArguments :: [ProtocolMessageArgument]
  }
  deriving (Eq, Show)

data RendezvousMessageEvidence = RendezvousMessageEvidence
  { rendezvousMessageEvidenceType :: Ty
  , rendezvousMessageEvidenceSemantics :: SemanticForm
  , rendezvousMessageEvidenceContract :: BoundaryMessageContract
  }
  deriving (Eq, Show)

rendezvousMessageEvidenceFromArgument
  :: ProtocolMessageArgument
  -> RendezvousMessageEvidence
rendezvousMessageEvidenceFromArgument argument = RendezvousMessageEvidence
  { rendezvousMessageEvidenceType = protocolMessageArgumentType argument
  , rendezvousMessageEvidenceSemantics = protocolMessageArgumentSemantics argument
  , rendezvousMessageEvidenceContract = protocolMessageArgumentBoundaryContract argument
  }

data RendezvousEndpointKernelFacts = RendezvousEndpointKernelFacts
  { rendezvousBinaryWellFormed :: Bool
  , rendezvousSenderProgression :: Bool
  , rendezvousReceiverProgression :: Bool
  , rendezvousSenderInstanceExact :: Bool
  , rendezvousReceiverInstanceExact :: Bool
  , rendezvousSenderRoleExact :: Bool
  , rendezvousReceiverRoleExact :: Bool
  , rendezvousCurrentSessionsDual :: Bool
  , rendezvousSuccessorSessionsDual :: Bool
  }
  deriving (Eq, Show)

data RendezvousParticipantKernelFacts = RendezvousParticipantKernelFacts
  { rendezvousParticipantClassificationValid :: Bool
  , rendezvousSenderParticipantExact :: Bool
  , rendezvousReceiverParticipantExact :: Bool
  , rendezvousSenderRoleOccurrenceExact :: Bool
  , rendezvousReceiverRoleOccurrenceExact :: Bool
  }
  deriving (Eq, Show)

data RendezvousMessageCoarseKernelFacts = RendezvousMessageCoarseKernelFacts
  { rendezvousMessageAccepted :: Bool
  , rendezvousCoarseStepValid :: Bool
  , rendezvousCoarseInstanceExact :: Bool
  , rendezvousCoarseSenderRoleExact :: Bool
  , rendezvousCoarseReceiverRoleExact :: Bool
  , rendezvousCoarseSenderProcessExact :: Bool
  , rendezvousCoarseReceiverProcessExact :: Bool
  }
  deriving (Eq, Show)

data CertifiedRendezvousCausality = CertifiedRendezvousCausality
  { certifiedRendezvousSenderProcess :: ProcessKey
  , certifiedRendezvousReceiverProcess :: ProcessKey
  }
  deriving (Eq, Show)

certifiedRendezvousEventKind :: CertifiedRendezvousCausality -> ProcessEventKind
certifiedRendezvousEventKind witness = SynchronousRendezvousEvent
  (certifiedRendezvousSenderProcess witness)
  (certifiedRendezvousReceiverProcess witness)

data CertifiedRendezvousResult = CertifiedRendezvousResult
  { certifiedRendezvousState :: ProcessCommunicationState
  , certifiedRendezvousCausality :: CertifiedRendezvousCausality
  }
  deriving (Eq, Show)

data ConcurrencyRendezvousCertificationError
  = ConcurrencyRendezvousActivationError ConcurrencyActivationCertificationError
  | ConcurrencyRendezvousProtocolError ProtocolFamilyError
  | ConcurrencyRendezvousProtocolInvariant
  | ConcurrencyRendezvousNativeError ProcessRendezvousError
  | ConcurrencyRendezvousReflectionProtocolError ProcessKey ProtocolCheckError
  | ConcurrencyRendezvousMessageError BoundaryMessageError
  | ConcurrencyRendezvousMessageTypeMismatch Ty Ty
  | ConcurrencyRendezvousMessageNotBoundToProtocol RendezvousMessageEvidence
  | ConcurrencyRendezvousMessageMissing ProcessKey
  | ConcurrencyRendezvousEndpointKernelDisagreement RendezvousEndpointKernelFacts
  | ConcurrencyRendezvousParticipantKernelDisagreement RendezvousParticipantKernelFacts
  | ConcurrencyRendezvousMessageCoarseKernelDisagreement RendezvousMessageCoarseKernelFacts
  | ConcurrencyRendezvousCertifiedKernelDisagreement Bool Bool Bool
  deriving (Eq, Show)

certifyRendezvousActivation
  :: ArchitectureInstanceGraph
  -> ProcessNetwork
  -> [ProcessActivationContract]
  -> [ProtocolRoleOccurrence]
  -> [ParticipantDeclaration]
  -> Either ConcurrencyRendezvousCertificationError CertifiedRendezvousActivation
certifyRendezvousActivation graph network contracts expected declarations =
  CertifiedRendezvousActivation <$> mapLeft ConcurrencyRendezvousActivationError
    (certifyConcurrencyActivation graph network contracts expected declarations)

certifyRendezvousProtocol
  :: GenericInstantiationPolicy
  -> BinaryProtocolFamily
  -> [ProtocolMessageArgument]
  -> [(GenericRequirement, GenericRequirementDisposition)]
  -> Either ConcurrencyRendezvousCertificationError CertifiedRendezvousProtocol
certifyRendezvousProtocol policy family arguments dispositions = do
  instanceValue <- mapLeft ConcurrencyRendezvousProtocolError $
    instantiateBinaryProtocol policy family arguments dispositions
  primary <- mapLeft ConcurrencyRendezvousProtocolError $
    projectProtocolRole instanceValue (protocolFamilyPrimaryRole family)
  peer <- mapLeft ConcurrencyRendezvousProtocolError $
    projectProtocolRole instanceValue (protocolFamilyPeerRole family)
  let primaryRole = protocolFamilyPrimaryRole family
      peerRole = protocolFamilyPeerRole family
      primarySession = protocolProjectionSession primary
      peerSession = protocolProjectionSession peer
  if primaryRole /= peerRole && peerSession == dualSession primarySession
    then Right CertifiedRendezvousProtocol
      { certifiedRendezvousProtocolInstance = instanceValue
      , certifiedRendezvousPrimaryRole = primaryRole
      , certifiedRendezvousPeerRole = peerRole
      , certifiedRendezvousPrimarySession = primarySession
      , certifiedRendezvousPeerSession = peerSession
      , certifiedRendezvousProtocolArguments = arguments
      }
    else Left ConcurrencyRendezvousProtocolInvariant

verifyRendezvousEndpointKernelFacts
  :: RendezvousEndpointKernelFacts
  -> Either ConcurrencyRendezvousCertificationError ()
verifyRendezvousEndpointKernelFacts facts
  | Kernel.decideRendezvousEndpointFactsByFacts
      (rendezvousBinaryWellFormed facts)
      (rendezvousSenderProgression facts)
      (rendezvousReceiverProgression facts)
      (rendezvousSenderInstanceExact facts)
      (rendezvousReceiverInstanceExact facts)
      (rendezvousSenderRoleExact facts)
      (rendezvousReceiverRoleExact facts)
      (rendezvousCurrentSessionsDual facts)
      (rendezvousSuccessorSessionsDual facts) = Right ()
  | otherwise = Left (ConcurrencyRendezvousEndpointKernelDisagreement facts)

verifyRendezvousParticipantKernelFacts
  :: RendezvousParticipantKernelFacts
  -> Either ConcurrencyRendezvousCertificationError ()
verifyRendezvousParticipantKernelFacts facts
  | Kernel.decideRendezvousParticipantFactsByFacts
      (rendezvousParticipantClassificationValid facts)
      (rendezvousSenderParticipantExact facts)
      (rendezvousReceiverParticipantExact facts)
      (rendezvousSenderRoleOccurrenceExact facts)
      (rendezvousReceiverRoleOccurrenceExact facts) = Right ()
  | otherwise = Left (ConcurrencyRendezvousParticipantKernelDisagreement facts)

verifyRendezvousMessageCoarseKernelFacts
  :: RendezvousMessageCoarseKernelFacts
  -> Either ConcurrencyRendezvousCertificationError ()
verifyRendezvousMessageCoarseKernelFacts facts
  | Kernel.decideRendezvousMessageCoarseFactsByFacts
      (rendezvousMessageAccepted facts)
      (rendezvousCoarseStepValid facts)
      (rendezvousCoarseInstanceExact facts)
      (rendezvousCoarseSenderRoleExact facts)
      (rendezvousCoarseReceiverRoleExact facts)
      (rendezvousCoarseSenderProcessExact facts)
      (rendezvousCoarseReceiverProcessExact facts) = Right ()
  | otherwise = Left (ConcurrencyRendezvousMessageCoarseKernelDisagreement facts)

verifyExactInternalRendezvousKernelFacts
  :: Bool
  -> Bool
  -> Bool
  -> Either ConcurrencyRendezvousCertificationError ()
verifyExactInternalRendezvousKernelFacts endpointValid participantsValid messageCoarseValid
  | Kernel.decideExactInternalRendezvousByFacts
      endpointValid participantsValid messageCoarseValid = Right ()
  | otherwise = Left
      (ConcurrencyRendezvousCertifiedKernelDisagreement
        endpointValid participantsValid messageCoarseValid)

-- | Certified Message-bearing joint rendezvous.  Select/offer remains a native
-- protocol feature, but the PHIL-CONC-RENDEZVOUS-001 production boundary is
-- intentionally fail-closed unless the synchronous action carries an exact
-- Message witness matching both endpoint session steps.
certifyProcessRendezvous
  :: CertifiedRendezvousActivation
  -> CertifiedRendezvousProtocol
  -> Map.Map ProcessKey ProtocolContext
  -> ProcessRendezvousRequest
  -> RendezvousMessageEvidence
  -> Either ConcurrencyRendezvousCertificationError CertifiedRendezvousResult
certifyProcessRendezvous activation protocol contexts request evidence = do
  beforeState <- mapLeft ConcurrencyRendezvousNativeError $
    communicationStateFromActivation
      (certifiedRendezvousActivationState activation) contexts
  updatedContexts <- mapLeft ConcurrencyRendezvousNativeError $
    checkProcessCommunication
      (certifiedRendezvousProtocolInstance protocol)
      (certifiedRendezvousActivationNetwork activation)
      contexts
      (JointProcessRendezvous request)
  let afterState = beforeState { communicationProtocolContexts = updatedContexts }
  certifyAcceptedRendezvous activation protocol beforeState afterState request Nothing evidence

certifyRestrictedProcessRendezvous
  :: CertifiedRendezvousActivation
  -> CertifiedRendezvousProtocol
  -> Map.Map ProcessKey ProtocolContext
  -> ProcessRendezvousRequest
  -> RestrictedMessageTransfer
  -> RendezvousMessageEvidence
  -> Either ConcurrencyRendezvousCertificationError CertifiedRendezvousResult
certifyRestrictedProcessRendezvous activation protocol contexts request transfer evidence = do
  beforeState <- mapLeft ConcurrencyRendezvousNativeError $
    communicationStateFromActivation
      (certifiedRendezvousActivationState activation) contexts
  afterState <- mapLeft ConcurrencyRendezvousNativeError $
    checkRestrictedProcessRendezvous
      (certifiedRendezvousProtocolInstance protocol)
      (certifiedRendezvousActivationNetwork activation)
      beforeState
      request
      transfer
  certifyAcceptedRendezvous
    activation protocol beforeState afterState request (Just transfer) evidence

certifyAcceptedRendezvous
  :: CertifiedRendezvousActivation
  -> CertifiedRendezvousProtocol
  -> ProcessCommunicationState
  -> ProcessCommunicationState
  -> ProcessRendezvousRequest
  -> Maybe RestrictedMessageTransfer
  -> RendezvousMessageEvidence
  -> Either ConcurrencyRendezvousCertificationError CertifiedRendezvousResult
certifyAcceptedRendezvous activation protocol beforeState afterState request transfer evidence = do
  let contextsBefore = communicationProtocolContexts beforeState
      contextsAfter = communicationProtocolContexts afterState
      network = certifiedRendezvousActivationNetwork activation
      instanceValue = certifiedRendezvousProtocolInstance protocol
      (sender, receiver) = requestSides request
      senderProcess = rendezvousProcess sender
      receiverProcess = rendezvousProcess receiver
      (senderAction, receiverAction) = protocolRequests request
  senderBefore <- requireContext senderProcess contextsBefore
  receiverBefore <- requireContext receiverProcess contextsBefore
  senderAfter <- requireContext senderProcess contextsAfter
  receiverAfter <- requireContext receiverProcess contextsAfter
  senderStep <- mapLeft
    (ConcurrencyRendezvousReflectionProtocolError senderProcess) $
    checkProtocolAction senderAction senderBefore
  receiverStep <- mapLeft
    (ConcurrencyRendezvousReflectionProtocolError receiverProcess) $
    checkProtocolAction receiverAction receiverBefore
  actualType <- reflectedMessageType senderProcess receiverProcess senderStep receiverStep
  verifyMessageEvidence protocol actualType evidence

  let endpointFacts = rendezvousEndpointFacts
        protocol sender receiver
        senderBefore receiverBefore senderAfter receiverAfter
        senderStep receiverStep
      participantFacts = rendezvousParticipantFacts
        activation protocol sender receiver senderStep receiverStep
      messageFacts = rendezvousMessageCoarseFacts
        protocol beforeState afterState sender receiver transfer endpointFacts participantFacts
  verifyRendezvousEndpointKernelFacts endpointFacts
  verifyRendezvousParticipantKernelFacts participantFacts
  verifyRendezvousMessageCoarseKernelFacts messageFacts
  verifyExactInternalRendezvousKernelFacts True True True
  pure CertifiedRendezvousResult
    { certifiedRendezvousState = afterState
    , certifiedRendezvousCausality = CertifiedRendezvousCausality
        { certifiedRendezvousSenderProcess = senderProcess
        , certifiedRendezvousReceiverProcess = receiverProcess
        }
    }
  where
    requireContext processKey contextMap = maybe
      (Left (ConcurrencyRendezvousNativeError
        (missingContextError processKey)))
      Right
      (Map.lookup processKey contextMap)

-- The native checker already emitted this exact diagnostic before reflection;
-- this sentinel is therefore only reachable if a pure-success result and the
-- reflected context map disagree, in which case the bridge still fails closed.
missingContextError :: ProcessKey -> ProcessRendezvousError
missingContextError = rendezvousMissingContext

rendezvousMissingContext :: ProcessKey -> ProcessRendezvousError
rendezvousMissingContext processKey =
  case impossibleMissingContext processKey of
    Left err -> err
    Right _ -> error "unreachable rendezvous missing-context sentinel"

impossibleMissingContext :: ProcessKey -> Either ProcessRendezvousError ()
impossibleMissingContext processKey =
  Left (RendezvousMissingProtocolContext processKey)

rendezvousEndpointFacts
  :: CertifiedRendezvousProtocol
  -> ProcessRendezvousSide
  -> ProcessRendezvousSide
  -> ProtocolContext
  -> ProtocolContext
  -> ProtocolContext
  -> ProtocolContext
  -> CheckedProtocolStep
  -> CheckedProtocolStep
  -> RendezvousEndpointKernelFacts
rendezvousEndpointFacts protocol sender receiver senderBefore receiverBefore senderAfter receiverAfter senderStep receiverStep =
  RendezvousEndpointKernelFacts
    { rendezvousBinaryWellFormed =
        certifiedRendezvousPrimaryRole protocol /= certifiedRendezvousPeerRole protocol
          && certifiedRendezvousPeerSession protocol
              == dualSession (certifiedRendezvousPrimarySession protocol)
    , rendezvousSenderProgression = progressionExact sender senderBefore senderAfter senderStep
    , rendezvousReceiverProgression = progressionExact receiver receiverBefore receiverAfter receiverStep
    , rendezvousSenderInstanceExact =
        protocolEndpointInstance (checkedProtocolPredecessor senderStep) == exactInstance
          && rendezvousInstance sender == exactInstance
    , rendezvousReceiverInstanceExact =
        protocolEndpointInstance (checkedProtocolPredecessor receiverStep) == exactInstance
          && rendezvousInstance receiver == exactInstance
    , rendezvousSenderRoleExact =
        protocolEndpointRole (checkedProtocolPredecessor senderStep)
          == certifiedRendezvousPrimaryRole protocol
          && rendezvousRole sender == certifiedRendezvousPrimaryRole protocol
    , rendezvousReceiverRoleExact =
        protocolEndpointRole (checkedProtocolPredecessor receiverStep)
          == certifiedRendezvousPeerRole protocol
          && rendezvousRole receiver == certifiedRendezvousPeerRole protocol
    , rendezvousCurrentSessionsDual =
        protocolEndpointSession (checkedProtocolPredecessor receiverStep)
          == dualSession (protocolEndpointSession (checkedProtocolPredecessor senderStep))
    , rendezvousSuccessorSessionsDual = successorSessionsDual senderStep receiverStep
    }
  where
    exactInstance = binaryProtocolInstanceRevision
      (certifiedRendezvousProtocolInstance protocol)

rendezvousParticipantFacts
  :: CertifiedRendezvousActivation
  -> CertifiedRendezvousProtocol
  -> ProcessRendezvousSide
  -> ProcessRendezvousSide
  -> CheckedProtocolStep
  -> CheckedProtocolStep
  -> RendezvousParticipantKernelFacts
rendezvousParticipantFacts activation protocol sender receiver senderStep receiverStep =
  RendezvousParticipantKernelFacts
    { rendezvousParticipantClassificationValid = True
    , rendezvousSenderParticipantExact = participantExact sender senderOccurrence
    , rendezvousReceiverParticipantExact = participantExact receiver receiverOccurrence
    , rendezvousSenderRoleOccurrenceExact =
        roleOccurrenceInstance senderOccurrence == exactInstance
          && roleOccurrenceRole senderOccurrence
              == protocolEndpointRole (checkedProtocolPredecessor senderStep)
    , rendezvousReceiverRoleOccurrenceExact =
        roleOccurrenceInstance receiverOccurrence == exactInstance
          && roleOccurrenceRole receiverOccurrence
              == protocolEndpointRole (checkedProtocolPredecessor receiverStep)
    }
  where
    exactInstance = binaryProtocolInstanceRevision
      (certifiedRendezvousProtocolInstance protocol)
    senderOccurrence = ProtocolRoleOccurrence exactInstance (rendezvousRole sender)
    receiverOccurrence = ProtocolRoleOccurrence exactInstance (rendezvousRole receiver)
    classifications = participantClassifications
      (certifiedRendezvousParticipantClassification activation)
    participantExact side occurrence =
      case Map.lookup occurrence classifications of
        Just (CheckedInternalParticipant checkedRole _ processKey) ->
          checkedRole == occurrence && processKey == rendezvousProcess side
        _ -> False

rendezvousMessageCoarseFacts
  :: CertifiedRendezvousProtocol
  -> ProcessCommunicationState
  -> ProcessCommunicationState
  -> ProcessRendezvousSide
  -> ProcessRendezvousSide
  -> Maybe RestrictedMessageTransfer
  -> RendezvousEndpointKernelFacts
  -> RendezvousParticipantKernelFacts
  -> RendezvousMessageCoarseKernelFacts
rendezvousMessageCoarseFacts protocol beforeState afterState sender receiver transfer endpointFacts participantFacts =
  RendezvousMessageCoarseKernelFacts
    { rendezvousMessageAccepted = True
    , rendezvousCoarseStepValid =
        not (Text.null (unProtocolInstanceRevision exactInstance))
          && rendezvousRole sender /= rendezvousRole receiver
          && rendezvousProcess sender /= rendezvousProcess receiver
          && restrictedOwnershipExact
    , rendezvousCoarseInstanceExact =
        rendezvousInstance sender == exactInstance
          && rendezvousInstance receiver == exactInstance
    , rendezvousCoarseSenderRoleExact =
        rendezvousSenderRoleExact endpointFacts
    , rendezvousCoarseReceiverRoleExact =
        rendezvousReceiverRoleExact endpointFacts
    , rendezvousCoarseSenderProcessExact =
        rendezvousSenderParticipantExact participantFacts
    , rendezvousCoarseReceiverProcessExact =
        rendezvousReceiverParticipantExact participantFacts
    }
  where
    exactInstance = binaryProtocolInstanceRevision
      (certifiedRendezvousProtocolInstance protocol)
    restrictedOwnershipExact = case transfer of
      Nothing -> True
      Just moved ->
        Map.lookup
          (restrictedMessageOccurrence moved)
          (communicationRestrictedOwners beforeState)
          == Just (rendezvousProcess sender, restrictedMessageSenderName moved)
        && Map.lookup
          (restrictedMessageOccurrence moved)
          (communicationRestrictedOwners afterState)
          == Just (rendezvousProcess receiver, restrictedMessageReceiverName moved)

verifyMessageEvidence
  :: CertifiedRendezvousProtocol
  -> Ty
  -> RendezvousMessageEvidence
  -> Either ConcurrencyRendezvousCertificationError ()
verifyMessageEvidence protocol actualType evidence = do
  if actualType == rendezvousMessageEvidenceType evidence
    then Right ()
    else Left (ConcurrencyRendezvousMessageTypeMismatch
      actualType (rendezvousMessageEvidenceType evidence))
  mapLeft ConcurrencyRendezvousMessageError $
    checkBoundaryMessageContract
      actualType
      (rendezvousMessageEvidenceSemantics evidence)
      (rendezvousMessageEvidenceContract evidence)
  if intrinsicBoundaryMessageType actualType
      || evidence `elem` map rendezvousMessageEvidenceFromArgument
          (certifiedRendezvousProtocolArguments protocol)
    then Right ()
    else Left (ConcurrencyRendezvousMessageNotBoundToProtocol evidence)

reflectedMessageType
  :: ProcessKey
  -> ProcessKey
  -> CheckedProtocolStep
  -> CheckedProtocolStep
  -> Either ConcurrencyRendezvousCertificationError Ty
reflectedMessageType senderProcess receiverProcess senderStep receiverStep =
  case ( stepMessage (checkedProtocolSessionStep senderStep)
       , stepMessage (checkedProtocolSessionStep receiverStep) ) of
    (Just senderMessage, Just receiverMessage)
      | messageType senderMessage == messageType receiverMessage ->
          Right (messageType senderMessage)
      | otherwise -> Left (ConcurrencyRendezvousMessageTypeMismatch
          (messageType senderMessage) (messageType receiverMessage))
    (Nothing, _) -> Left (ConcurrencyRendezvousMessageMissing senderProcess)
    (_, Nothing) -> Left (ConcurrencyRendezvousMessageMissing receiverProcess)

progressionExact
  :: ProcessRendezvousSide
  -> ProtocolContext
  -> ProtocolContext
  -> CheckedProtocolStep
  -> Bool
progressionExact side before after step =
  lookupProtocolEndpoint predecessor before == Just checkedPredecessor
    && protocolEndpointName checkedPredecessor == predecessor
    && lookupProtocolEndpoint predecessor after == Nothing
    && case checkedProtocolSuccessor step of
      Just successor ->
        protocolEndpointName successor == rendezvousSuccessor side
          && lookupProtocolEndpoint (rendezvousSuccessor side) after == Just successor
      Nothing -> False
  where
    predecessor = rendezvousEndpoint side
    checkedPredecessor = checkedProtocolPredecessor step

successorSessionsDual :: CheckedProtocolStep -> CheckedProtocolStep -> Bool
successorSessionsDual senderStep receiverStep =
  case (checkedProtocolSuccessor senderStep, checkedProtocolSuccessor receiverStep) of
    (Just senderSuccessor, Just receiverSuccessor) ->
      protocolEndpointSession receiverSuccessor
        == dualSession (protocolEndpointSession senderSuccessor)
    _ -> False

requestSides :: ProcessRendezvousRequest -> (ProcessRendezvousSide, ProcessRendezvousSide)
requestSides request = case request of
  SendReceiveRendezvous sender receiver -> (sender, receiver)
  SelectOfferRendezvous selector offerer _ -> (selector, offerer)

protocolRequests
  :: ProcessRendezvousRequest
  -> (ProtocolActionRequest, ProtocolActionRequest)
protocolRequests request = case request of
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

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
