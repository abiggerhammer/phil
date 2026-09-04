{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ConcurrencyActivationCertification
  ( ActivationContextKernelFacts (..)
  , ParticipantClassificationKernelFacts (..)
  , ConcurrencyActivationCertificationError (..)
  , ConcurrencyActivationCertificationResult (..)
  , activationContextKernelFacts
  , participantClassificationKernelFacts
  , verifyActivationContextKernelFacts
  , verifyParticipantClassificationKernelFacts
  , verifyCertifiedConcurrencyActivationKernelFacts
  , activateProcessStateCertified
  , checkParticipantClassificationsCertified
  , certifyConcurrencyActivation
  ) where

import qualified ConcurrencyActivationKernel as Kernel
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Process
  ( ActivationStatus (..)
  , ProcessKey (..)
  , ProcessNetwork (..)
  , ProcessOccurrence (..)
  )
import Phil.Core.ProcessActivation
  ( ActivationBinding (..)
  , ActivationBindingOrigin (..)
  , ActivationReachability (..)
  , ProcessActivationContract (..)
  , ProcessActivationError
  , ProcessActivationState (..)
  , activateProcessState
  )
import Phil.Core.ProcessParticipants
  ( CheckedParticipant (..)
  , ParticipantClassification (..)
  , ParticipantClassificationError
  , ParticipantDeclaration
  , ProtocolRoleOccurrence (..)
  , checkParticipantClassifications
  )
import Phil.Core.Protocol
  ( ProtocolInstanceRevision (..)
  , ProtocolRoleKey (..)
  )
import Phil.Core.Static
  ( ArchitectureInstanceGraph
  , ArchitectureInstanceIdentity (..)
  )
import Phil.Core.Syntax (Mode (..))

data ActivationContextKernelFacts = ActivationContextKernelFacts
  { activationPopulationValid :: Bool
  , activationBindingsExplicit :: Bool
  , activationBindingProcessesActivated :: Bool
  , activationRestrictedBindingsExact :: Bool
  , activationNoInventedRestrictedOwner :: Bool
  , activationDirectStatefulBindingsExact :: Bool
  , activationNoInventedDirectStatefulOwner :: Bool
  }
  deriving (Eq, Show)

data ParticipantClassificationKernelFacts = ParticipantClassificationKernelFacts
  { participantClassificationExact :: Bool
  , participantInternalActivated :: Bool
  , participantInternalStatic :: Bool
  , participantNoEmptyRole :: Bool
  }
  deriving (Eq, Show)

data ConcurrencyActivationCertificationError
  = ConcurrencyActivationNativeError ProcessActivationError
  | ConcurrencyActivationKernelDisagreement ActivationContextKernelFacts
  | ConcurrencyParticipantNativeError ParticipantClassificationError
  | ConcurrencyParticipantKernelDisagreement ParticipantClassificationKernelFacts
  | ConcurrencyActivationCertifiedKernelDisagreement Bool Bool
  deriving (Eq, Show)

data ConcurrencyActivationCertificationResult = ConcurrencyActivationCertificationResult
  { certifiedActivationNetwork :: ProcessNetwork
  , certifiedActivationState :: ProcessActivationState
  , certifiedParticipantClassification :: ParticipantClassification
  }
  deriving (Eq, Show)

activationContextKernelFacts
  :: ProcessNetwork
  -> [ProcessActivationContract]
  -> ProcessNetwork
  -> ProcessActivationState
  -> ActivationContextKernelFacts
activationContextKernelFacts before contracts after state =
  ActivationContextKernelFacts
    { activationPopulationValid = populationValid
    , activationBindingsExplicit = all (explicitOrigin . activationBindingOrigin . snd) bindings
    , activationBindingProcessesActivated = all bindingProcessActivated bindings
    , activationRestrictedBindingsExact = all restrictedBindingExact restrictedBindings
    , activationNoInventedRestrictedOwner = all restrictedOwnerExplained (Map.toList restrictedOwners)
    , activationDirectStatefulBindingsExact = all directBindingExact directBindings
    , activationNoInventedDirectStatefulOwner = all directOwnerExplained (Map.toList directOwners)
    }
  where
    bindings = flattenBindings contracts
    restrictedBindings = filter (isRestricted . snd) bindings
    directBindings =
      [ (processKey, binding, statefulKey)
      | (processKey, binding) <- bindings
      , DirectStatefulReachability statefulKey <- [activationReachability binding]
      ]
    restrictedOwners = activationRestrictedOwners state
    directOwners = activationDirectStatefulReachability state
    beforePopulation = processNetworkPopulation before
    afterPopulation = processNetworkPopulation after
    populationValid =
      not (Map.null beforePopulation)
        && processNetworkRoot before == processNetworkRoot after
        && Map.keysSet beforePopulation == Map.keysSet afterPopulation
        && all keyedOccurrenceValid (Map.toList beforePopulation)
        && all ((== NotActivated) . processOccurrenceActivation) (Map.elems beforePopulation)
        && all ((== Active) . processOccurrenceActivation) (Map.elems afterPopulation)
        && all staticOccurrencePreserved (Map.toList beforePopulation)
    keyedOccurrenceValid (processKey, occurrence) =
      processKey == processOccurrenceKey occurrence
        && not (Text.null (unProcessKey processKey))
    staticOccurrencePreserved (processKey, occurrence) =
      case Map.lookup processKey afterPopulation of
        Nothing -> False
        Just activated -> sameStaticOccurrence occurrence activated
    bindingProcessActivated (processKey, _) =
      case Map.lookup processKey afterPopulation of
        Just occurrence -> processOccurrenceActivation occurrence == Active
        Nothing -> False
    restrictedBindingExact (processKey, binding) =
      Map.lookup (activationOccurrenceKey binding) restrictedOwners
        == Just (processKey, activationLocalName binding)
    restrictedOwnerExplained (occurrenceKey, (processKey, localName)) =
      any
        (\(candidateProcess, binding) ->
          candidateProcess == processKey
            && activationOccurrenceKey binding == occurrenceKey
            && activationLocalName binding == localName
            && isRestricted binding)
        bindings
    directBindingExact (processKey, _, statefulKey) =
      case Map.lookup statefulKey directOwners of
        Just (actualProcess, _) -> actualProcess == processKey
        Nothing -> False
    directOwnerExplained (statefulKey, (processKey, _)) =
      any
        (\(candidateProcess, binding, candidateStateful) ->
          candidateProcess == processKey
            && candidateStateful == statefulKey
            && case activationReachability binding of
              DirectStatefulReachability _ -> True
              _ -> False)
        directBindings

participantClassificationKernelFacts
  :: ProcessNetwork
  -> [ProtocolRoleOccurrence]
  -> ParticipantClassification
  -> ParticipantClassificationKernelFacts
participantClassificationKernelFacts network expected checked =
  ParticipantClassificationKernelFacts
    { participantClassificationExact = classificationExact
    , participantInternalActivated = all internalActivated classifications
    , participantInternalStatic = all internalStatic classifications
    , participantNoEmptyRole = all (not . emptyRoleOccurrence) expected
    }
  where
    classifications = Map.toList (participantClassifications checked)
    expectedSet = Set.fromList expected
    classificationExact =
      length expected == Set.size expectedSet
        && expectedSet == Map.keysSet (participantClassifications checked)
        && all (\(role, participant) -> checkedParticipantRole participant == role) classifications
    population = processNetworkPopulation network
    internalActivated (_, participant) =
      case participant of
        CheckedExternalParticipant _ -> True
        CheckedInternalParticipant _ _ processKey ->
          case Map.lookup processKey population of
            Just occurrence -> processOccurrenceActivation occurrence == Active
            Nothing -> False
    internalStatic (_, participant) =
      case participant of
        CheckedExternalParticipant _ -> True
        CheckedInternalParticipant _ targetKey processKey ->
          case Map.lookup processKey population of
            Nothing -> False
            Just occurrence ->
              processOccurrenceKey occurrence == processKey
                && identityInstanceKey (processOccurrenceTarget occurrence) == targetKey

verifyActivationContextKernelFacts
  :: ActivationContextKernelFacts
  -> Either ConcurrencyActivationCertificationError ()
verifyActivationContextKernelFacts facts
  | explicitAccepted && restrictedAccepted && directAccepted && aggregateAccepted = Right ()
  | otherwise = Left (ConcurrencyActivationKernelDisagreement facts)
  where
    explicitAccepted =
      Kernel.decideActivationBindingExplicitByFacts
        (activationBindingsExplicit facts)
    restrictedAccepted =
      Kernel.decideRestrictedInitialOwnershipByFacts
        (activationRestrictedBindingsExact facts)
        (activationNoInventedRestrictedOwner facts)
    directAccepted =
      Kernel.decideDirectStatefulOwnershipByFacts
        (activationDirectStatefulBindingsExact facts)
        (activationNoInventedDirectStatefulOwner facts)
    aggregateAccepted =
      Kernel.decideActivationContextByFacts
        (activationPopulationValid facts)
        (activationBindingsExplicit facts)
        (activationBindingProcessesActivated facts)
        (activationRestrictedBindingsExact facts)
        (activationNoInventedRestrictedOwner facts)
        (activationDirectStatefulBindingsExact facts)
        (activationNoInventedDirectStatefulOwner facts)

verifyParticipantClassificationKernelFacts
  :: ParticipantClassificationKernelFacts
  -> Either ConcurrencyActivationCertificationError ()
verifyParticipantClassificationKernelFacts facts
  | Kernel.decideParticipantClassificationByFacts
      (participantClassificationExact facts)
      (participantInternalActivated facts)
      (participantInternalStatic facts)
      (participantNoEmptyRole facts) = Right ()
  | otherwise = Left (ConcurrencyParticipantKernelDisagreement facts)

verifyCertifiedConcurrencyActivationKernelFacts
  :: Bool
  -> Bool
  -> Either ConcurrencyActivationCertificationError ()
verifyCertifiedConcurrencyActivationKernelFacts activationValid participantsValid
  | Kernel.decideCertifiedConcurrencyActivationByFacts activationValid participantsValid = Right ()
  | otherwise = Left
      (ConcurrencyActivationCertifiedKernelDisagreement activationValid participantsValid)

activateProcessStateCertified
  :: ProcessNetwork
  -> [ProcessActivationContract]
  -> Either
      ConcurrencyActivationCertificationError
      (ProcessNetwork, ProcessActivationState)
activateProcessStateCertified network contracts = do
  (activated, state) <- mapLeft ConcurrencyActivationNativeError $
    activateProcessState network contracts
  verifyActivationContextKernelFacts
    (activationContextKernelFacts network contracts activated state)
  pure (activated, state)

checkParticipantClassificationsCertified
  :: ArchitectureInstanceGraph
  -> ProcessNetwork
  -> [ProtocolRoleOccurrence]
  -> [ParticipantDeclaration]
  -> Either ConcurrencyActivationCertificationError ParticipantClassification
checkParticipantClassificationsCertified graph network expected declarations = do
  checked <- mapLeft ConcurrencyParticipantNativeError $
    checkParticipantClassifications graph network expected declarations
  verifyParticipantClassificationKernelFacts
    (participantClassificationKernelFacts network expected checked)
  pure checked

certifyConcurrencyActivation
  :: ArchitectureInstanceGraph
  -> ProcessNetwork
  -> [ProcessActivationContract]
  -> [ProtocolRoleOccurrence]
  -> [ParticipantDeclaration]
  -> Either ConcurrencyActivationCertificationError ConcurrencyActivationCertificationResult
certifyConcurrencyActivation graph network contracts expected declarations = do
  (activated, state) <- activateProcessStateCertified network contracts
  participants <- checkParticipantClassificationsCertified
    graph activated expected declarations
  verifyCertifiedConcurrencyActivationKernelFacts True True
  pure ConcurrencyActivationCertificationResult
    { certifiedActivationNetwork = activated
    , certifiedActivationState = state
    , certifiedParticipantClassification = participants
    }

flattenBindings :: [ProcessActivationContract] -> [(ProcessKey, ActivationBinding)]
flattenBindings contracts =
  [ (activationContractProcess contract, binding)
  | contract <- contracts
  , binding <- activationContractBindings contract
  ]

explicitOrigin :: ActivationBindingOrigin -> Bool
explicitOrigin origin =
  case origin of
    AmbientActivationOrigin _ -> False
    _ -> True

isRestricted :: ActivationBinding -> Bool
isRestricted binding =
  case checkedBindingMode (activationCheckedTypeMode binding) of
    Unrestricted -> False
    Affine -> True
    Linear -> True

sameStaticOccurrence :: ProcessOccurrence -> ProcessOccurrence -> Bool
sameStaticOccurrence before after =
  processOccurrenceKey before == processOccurrenceKey after
    && processOccurrenceRootRevision before == processOccurrenceRootRevision after
    && processOccurrenceOwner before == processOccurrenceOwner after
    && processOccurrenceTarget before == processOccurrenceTarget after

emptyRoleOccurrence :: ProtocolRoleOccurrence -> Bool
emptyRoleOccurrence occurrence =
  Text.null (unProtocolInstanceRevision (roleOccurrenceInstance occurrence))
    && Text.null (unProtocolRoleKey (roleOccurrenceRole occurrence))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
