{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.ProtocolStateCorrespondence
  ( ProtocolStateStageRevision (..)
  , ProtocolInstanceRevision (..)
  , ProtocolRoleKey (..)
  , LocalSessionRevision (..)
  , EndpointOccurrenceKey (..)
  , ProtocolTransitionKey (..)
  , ProtocolEndpointState (..)
  , ProtocolTargetSite (..)
  , ProtocolAction (..)
  , ProtocolTransitionOutcome (..)
  , ProtocolCorrespondenceBasis (..)
  , ProtocolTransitionBinding (..)
  , ProtocolStateStageBundle (..)
  , ProtocolStateVerificationError (..)
  , deriveProtocolStateStageRevision
  , makeProtocolStateStageBundle
  , verifyProtocolStateStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.AuthorityEffectCorrespondence
  ( AuthorityEffectStageBundle (..)
  )
import Phil.Systems.BranchResourceFailure
  ( BranchResourceStageBundle (..)
  )
import Phil.Systems.ControlStateProjection
  ( ControlStateProjectionError
  , ControlStateStageBundle (..)
  , ControlStateStageRevision (..)
  , verifyControlStateStageBundle
  )
import Phil.Systems.IR
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import Phil.Systems.ProviderCallCorrespondence
  ( ProviderCallStageBundle (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  , SystemsValueRef (..)
  )

newtype ProtocolStateStageRevision = ProtocolStateStageRevision
  { unProtocolStateStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProtocolInstanceRevision = ProtocolInstanceRevision
  { unProtocolInstanceRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProtocolRoleKey = ProtocolRoleKey
  { unProtocolRoleKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype LocalSessionRevision = LocalSessionRevision
  { unLocalSessionRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype EndpointOccurrenceKey = EndpointOccurrenceKey
  { unEndpointOccurrenceKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ProtocolTransitionKey = ProtocolTransitionKey
  { unProtocolTransitionKey :: Text
  }
  deriving (Eq, Ord, Show)

data ProtocolEndpointState = ProtocolEndpointState
  { protocolEndpointOccurrence :: EndpointOccurrenceKey
  , protocolEndpointInstance :: ProtocolInstanceRevision
  , protocolEndpointRole :: ProtocolRoleKey
  , protocolEndpointSession :: LocalSessionRevision
  }
  deriving (Eq, Ord, Show)

data ProtocolTargetSite
  = ProtocolOperationSite Text BlockId Int
  | ProtocolTerminatorSite Text BlockId
  deriving (Eq, Ord, Show)

data ProtocolAction
  = ProtocolReceiveCommit Text
  | ProtocolSelect Text
  | ProtocolOffer (Set Text)
  | ProtocolReceiveExact
  | ProtocolSendExact
  | ProtocolOpaqueAction Text
  deriving (Eq, Ord, Show)

data ProtocolTransitionOutcome
  = ProtocolSuccessor EndpointOccurrenceKey
  | ProtocolTerminal Text
  deriving (Eq, Ord, Show)

data ProtocolCorrespondenceBasis
  = CheckedProtocolCorrespondence Text
  | CheckedLegacyOpaqueProtocolBridge Text
  | RuntimeTransportCoincidence Text
  deriving (Eq, Ord, Show)

data ProtocolTransitionBinding = ProtocolTransitionBinding
  { protocolTransitionKey :: ProtocolTransitionKey
  , protocolTransitionPredecessor :: EndpointOccurrenceKey
  , protocolTransitionAction :: ProtocolAction
  , protocolTransitionTargetSite :: ProtocolTargetSite
  , protocolTransitionTransport :: SystemsValueRef
  , protocolTransitionOutcomes :: Map Text ProtocolTransitionOutcome
  , protocolTransitionBasis :: ProtocolCorrespondenceBasis
  }
  deriving (Eq, Ord, Show)

data ProtocolStateStageBundle = ProtocolStateStageBundle
  { protocolStateStageBase :: ControlStateStageBundle
  , protocolStateStageRevision :: ProtocolStateStageRevision
  , protocolStateStageEndpoints :: Map EndpointOccurrenceKey ProtocolEndpointState
  , protocolStateStageTransitions :: Map ProtocolTransitionKey ProtocolTransitionBinding
  }
  deriving (Eq, Show)

data ProtocolStateVerificationError
  = ProtocolStateBaseStageError ControlStateProjectionError
  | ProtocolStateStageRevisionMismatch ProtocolStateStageRevision ProtocolStateStageRevision
  | ProtocolEndpointMapKeyMismatch EndpointOccurrenceKey EndpointOccurrenceKey
  | ProtocolEndpointEmptyInstance EndpointOccurrenceKey
  | ProtocolEndpointEmptyRole EndpointOccurrenceKey
  | ProtocolEndpointEmptySession EndpointOccurrenceKey
  | ProtocolTransitionMapKeyMismatch ProtocolTransitionKey ProtocolTransitionKey
  | ProtocolTransitionUnknownPredecessor ProtocolTransitionKey EndpointOccurrenceKey
  | ProtocolTransitionEmptyOutcomes ProtocolTransitionKey
  | ProtocolTransitionEmptyBasis ProtocolTransitionKey
  | ProtocolTransitionRuntimeCoincidenceRejected ProtocolTransitionKey Text
  | ProtocolTransitionUnknownFunction ProtocolTransitionKey Text
  | ProtocolTransitionUnknownBlock ProtocolTransitionKey BlockId
  | ProtocolTransitionUnknownOperation ProtocolTransitionKey Int
  | ProtocolTransitionTransportFunctionMismatch ProtocolTransitionKey SystemsValueRef Text
  | ProtocolTransitionUnknownTransport ProtocolTransitionKey SystemsValueRef
  | ProtocolTransitionValueNotTransport ProtocolTransitionKey SystemsValueRef SystemsValueRole
  | ProtocolTransitionUnsupportedTarget ProtocolTransitionKey ProtocolTargetSite
  | ProtocolTransitionActionMismatch ProtocolTransitionKey ProtocolAction
  | ProtocolTransitionOpaqueBridgeRequired ProtocolTransitionKey
  | ProtocolTransitionTypedBasisRequired ProtocolTransitionKey
  | ProtocolTransitionTransportUseMismatch ProtocolTransitionKey ValueId Int
  | ProtocolTransitionOutcomeDomainMismatch ProtocolTransitionKey (Set Text) (Set Text)
  | ProtocolTransitionUnknownSuccessor ProtocolTransitionKey Text EndpointOccurrenceKey
  | ProtocolTransitionReusesPredecessorAsSuccessor ProtocolTransitionKey EndpointOccurrenceKey
  | ProtocolTransitionInstanceMismatch ProtocolTransitionKey EndpointOccurrenceKey ProtocolInstanceRevision ProtocolInstanceRevision
  | ProtocolTransitionRoleMismatch ProtocolTransitionKey EndpointOccurrenceKey ProtocolRoleKey ProtocolRoleKey
  | ProtocolTransitionTargetSiteShared ProtocolTargetSite (Set ProtocolTransitionKey)
  | ProtocolEndpointConsumedMoreThanOnce EndpointOccurrenceKey (Set ProtocolTransitionKey)
  | ProtocolEndpointProducedMoreThanOnce EndpointOccurrenceKey (Set ProtocolTransitionKey)
  | ProtocolEndpointLineageCycle EndpointOccurrenceKey
  deriving (Eq, Show)

deriveProtocolStateStageRevision
  :: ProtocolStateStageBundle
  -> ProtocolStateStageRevision
deriveProtocolStateStageRevision bundle = ProtocolStateStageRevision
  ("phil.phase1.protocol-state-stage.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom
          (unControlStateStageRevision
            (controlStateStageRevision (protocolStateStageBase bundle))))
      , ("endpoints", SemanticRecord (Map.fromList
          [ (unEndpointOccurrenceKey key, semanticEndpoint endpoint)
          | (key, endpoint) <- Map.toAscList (protocolStateStageEndpoints bundle)
          ]))
      , ("transitions", SemanticRecord (Map.fromList
          [ (unProtocolTransitionKey key, semanticTransition transition)
          | (key, transition) <- Map.toAscList (protocolStateStageTransitions bundle)
          ]))
      ])))

makeProtocolStateStageBundle
  :: ControlStateStageBundle
  -> Map EndpointOccurrenceKey ProtocolEndpointState
  -> Map ProtocolTransitionKey ProtocolTransitionBinding
  -> ProtocolStateStageBundle
makeProtocolStateStageBundle base endpoints transitions = provisional
  { protocolStateStageRevision = deriveProtocolStateStageRevision provisional }
  where
    provisional = ProtocolStateStageBundle
      { protocolStateStageBase = base
      , protocolStateStageRevision = ProtocolStateStageRevision "pending"
      , protocolStateStageEndpoints = endpoints
      , protocolStateStageTransitions = transitions
      }

verifyProtocolStateStageBundle
  :: ProtocolStateStageBundle
  -> Either ProtocolStateVerificationError ()
verifyProtocolStateStageBundle bundle = do
  mapLeft ProtocolStateBaseStageError $
    verifyControlStateStageBundle (protocolStateStageBase bundle)
  requireEqual ProtocolStateStageRevisionMismatch
    (deriveProtocolStateStageRevision bundle)
    (protocolStateStageRevision bundle)
  mapM_ checkEndpoint (Map.toAscList endpoints)
  mapM_ (checkTransition bundle) (Map.toAscList transitions)
  checkUniqueTargetSites transitions
  checkEndpointConsumption transitions
  checkEndpointProduction transitions
  checkAcyclicLineage endpoints transitions
  where
    endpoints = protocolStateStageEndpoints bundle
    transitions = protocolStateStageTransitions bundle

checkEndpoint
  :: (EndpointOccurrenceKey, ProtocolEndpointState)
  -> Either ProtocolStateVerificationError ()
checkEndpoint (key, endpoint) = do
  requireEqual ProtocolEndpointMapKeyMismatch key (protocolEndpointOccurrence endpoint)
  if Text.null (unProtocolInstanceRevision (protocolEndpointInstance endpoint))
    then Left (ProtocolEndpointEmptyInstance key)
    else Right ()
  if Text.null (unProtocolRoleKey (protocolEndpointRole endpoint))
    then Left (ProtocolEndpointEmptyRole key)
    else Right ()
  if Text.null (unLocalSessionRevision (protocolEndpointSession endpoint))
    then Left (ProtocolEndpointEmptySession key)
    else Right ()

checkTransition
  :: ProtocolStateStageBundle
  -> (ProtocolTransitionKey, ProtocolTransitionBinding)
  -> Either ProtocolStateVerificationError ()
checkTransition bundle (key, transition) = do
  requireEqual ProtocolTransitionMapKeyMismatch key (protocolTransitionKey transition)
  predecessor <- maybe
    (Left (ProtocolTransitionUnknownPredecessor key (protocolTransitionPredecessor transition)))
    Right
    (Map.lookup (protocolTransitionPredecessor transition) endpoints)
  if Map.null (protocolTransitionOutcomes transition)
    then Left (ProtocolTransitionEmptyOutcomes key)
    else Right ()
  checkBasis key (protocolTransitionBasis transition)
  expectedDomain <- checkTargetSite bundle key transition
  case expectedDomain of
    Nothing -> Right ()
    Just domain -> requireEqual (ProtocolTransitionOutcomeDomainMismatch key)
      domain (Map.keysSet (protocolTransitionOutcomes transition))
  mapM_ (checkOutcome key predecessor)
    (Map.toAscList (protocolTransitionOutcomes transition))
  where
    endpoints = protocolStateStageEndpoints bundle
    checkOutcome transitionKey predecessor (label, outcome) = case outcome of
      ProtocolTerminal _ -> Right ()
      ProtocolSuccessor successorKey -> do
        successor <- maybe
          (Left (ProtocolTransitionUnknownSuccessor transitionKey label successorKey))
          Right
          (Map.lookup successorKey endpoints)
        if successorKey == protocolEndpointOccurrence predecessor
          then Left (ProtocolTransitionReusesPredecessorAsSuccessor transitionKey successorKey)
          else Right ()
        requireEqual
          (ProtocolTransitionInstanceMismatch transitionKey successorKey)
          (protocolEndpointInstance predecessor)
          (protocolEndpointInstance successor)
        requireEqual
          (ProtocolTransitionRoleMismatch transitionKey successorKey)
          (protocolEndpointRole predecessor)
          (protocolEndpointRole successor)

checkBasis
  :: ProtocolTransitionKey
  -> ProtocolCorrespondenceBasis
  -> Either ProtocolStateVerificationError ()
checkBasis key basis = case basis of
  CheckedProtocolCorrespondence revision
    | Text.null revision -> Left (ProtocolTransitionEmptyBasis key)
    | otherwise -> Right ()
  CheckedLegacyOpaqueProtocolBridge evidence
    | Text.null evidence -> Left (ProtocolTransitionEmptyBasis key)
    | otherwise -> Right ()
  RuntimeTransportCoincidence reason ->
    Left (ProtocolTransitionRuntimeCoincidenceRejected key reason)

checkTargetSite
  :: ProtocolStateStageBundle
  -> ProtocolTransitionKey
  -> ProtocolTransitionBinding
  -> Either ProtocolStateVerificationError (Maybe (Set Text))
checkTargetSite bundle key transition = do
  let site = protocolTransitionTargetSite transition
      transportRef = protocolTransitionTransport transition
      functionName = targetSiteFunction site
  if systemsValueRefFunction transportRef /= functionName
    then Left (ProtocolTransitionTransportFunctionMismatch key transportRef functionName)
    else Right ()
  function <- lookupFunction key functionName program
  transport <- maybe
    (Left (ProtocolTransitionUnknownTransport key transportRef))
    Right
    (Map.lookup (systemsValueRefValue transportRef) (systemsFunctionValues function))
  if systemsValueRole transport /= TransportHandle
    then Left (ProtocolTransitionValueNotTransport key transportRef (systemsValueRole transport))
    else Right ()
  case site of
    ProtocolOperationSite _ blockId operationIndex -> do
      blockValue <- lookupBlock key blockId function
      operation <- maybe
        (Left (ProtocolTransitionUnknownOperation key operationIndex))
        Right
        (indexMaybe operationIndex (systemsBlockOps blockValue))
      checkOperationSite key transition function operation
    ProtocolTerminatorSite _ blockId -> do
      blockValue <- lookupBlock key blockId function
      checkTerminatorSite key transition (systemsBlockTerminator blockValue)
  where
    program = systemsArtifactProgram (protocolStageArtifact (protocolStateStageBase bundle))

checkOperationSite
  :: ProtocolTransitionKey
  -> ProtocolTransitionBinding
  -> SystemsFunction
  -> SystemsOp
  -> Either ProtocolStateVerificationError (Maybe (Set Text))
checkOperationSite key transition function operation =
  let transport = systemsValueRefValue (protocolTransitionTransport transition)
      action = protocolTransitionAction transition
      basis = protocolTransitionBasis transition
  in case operation of
    OpCommitIngress pending actualTransport _ -> do
      requireTypedBasis key basis
      requireTransportExactlyOnce key transport [actualTransport]
      pendingValue <- maybe
        (Left (ProtocolTransitionActionMismatch key action))
        Right
        (Map.lookup pending (systemsFunctionValues function))
      case (action, systemsValueRole pendingValue) of
        (ProtocolReceiveCommit expectedMessage, PendingIngress actualMessage)
          | expectedMessage == actualMessage -> Right (Just (Set.singleton "success"))
        _ -> Left (ProtocolTransitionActionMismatch key action)
    OpSessionSelect actualTransport actualLabel _ _ -> do
      requireTypedBasis key basis
      requireTransportExactlyOnce key transport [actualTransport]
      case action of
        ProtocolSelect expectedLabel
          | expectedLabel == actualLabel -> Right (Just (Set.singleton "success"))
        _ -> Left (ProtocolTransitionActionMismatch key action)
    OpRuntimeCall _ inputs _ _ _ -> do
      requireOpaqueBasis key basis
      requireTransportExactlyOnce key transport inputs
      case action of
        ProtocolOpaqueAction semanticAction
          | not (Text.null semanticAction) -> Right Nothing
        _ -> Left (ProtocolTransitionActionMismatch key action)
    _ -> Left (ProtocolTransitionUnsupportedTarget key (protocolTransitionTargetSite transition))

checkTerminatorSite
  :: ProtocolTransitionKey
  -> ProtocolTransitionBinding
  -> SystemsTerminator
  -> Either ProtocolStateVerificationError (Maybe (Set Text))
checkTerminatorSite key transition terminator = do
  requireTypedBasis key (protocolTransitionBasis transition)
  let transport = systemsValueRefValue (protocolTransitionTransport transition)
      action = protocolTransitionAction transition
  case terminator of
    TermSessionOffer actualTransport arms -> do
      requireTransportExactlyOnce key transport [actualTransport]
      case action of
        ProtocolOffer labels
          | labels == Map.keysSet arms -> Right (Just labels)
        _ -> Left (ProtocolTransitionActionMismatch key action)
    TermReceiveExact actualTransport _ _ _ _ _ -> do
      requireTransportExactlyOnce key transport [actualTransport]
      case action of
        ProtocolReceiveExact -> Right (Just (Set.fromList ["success", "failure"]))
        _ -> Left (ProtocolTransitionActionMismatch key action)
    TermSendExact actualTransport _ _ _ _ -> do
      requireTransportExactlyOnce key transport [actualTransport]
      case action of
        ProtocolSendExact -> Right (Just (Set.fromList ["success", "failure"]))
        _ -> Left (ProtocolTransitionActionMismatch key action)
    _ -> Left (ProtocolTransitionUnsupportedTarget key (protocolTransitionTargetSite transition))

requireTypedBasis
  :: ProtocolTransitionKey
  -> ProtocolCorrespondenceBasis
  -> Either ProtocolStateVerificationError ()
requireTypedBasis key basis = case basis of
  CheckedProtocolCorrespondence revision
    | not (Text.null revision) -> Right ()
  _ -> Left (ProtocolTransitionTypedBasisRequired key)

requireOpaqueBasis
  :: ProtocolTransitionKey
  -> ProtocolCorrespondenceBasis
  -> Either ProtocolStateVerificationError ()
requireOpaqueBasis key basis = case basis of
  CheckedLegacyOpaqueProtocolBridge evidence
    | not (Text.null evidence) -> Right ()
  _ -> Left (ProtocolTransitionOpaqueBridgeRequired key)

requireTransportExactlyOnce
  :: ProtocolTransitionKey
  -> ValueId
  -> [ValueId]
  -> Either ProtocolStateVerificationError ()
requireTransportExactlyOnce key transport values =
  let count = length (filter (== transport) values)
  in if count == 1
      then Right ()
      else Left (ProtocolTransitionTransportUseMismatch key transport count)

checkUniqueTargetSites
  :: Map ProtocolTransitionKey ProtocolTransitionBinding
  -> Either ProtocolStateVerificationError ()
checkUniqueTargetSites transitions =
  case
    [ (site, keys)
    | (site, keys) <- Map.toAscList bySite
    , Set.size keys > 1
    ] of
    [] -> Right ()
    (site, keys) : _ -> Left (ProtocolTransitionTargetSiteShared site keys)
  where
    bySite = Map.fromListWith Set.union
      [ (protocolTransitionTargetSite transition, Set.singleton key)
      | (key, transition) <- Map.toAscList transitions
      ]

checkEndpointConsumption
  :: Map ProtocolTransitionKey ProtocolTransitionBinding
  -> Either ProtocolStateVerificationError ()
checkEndpointConsumption transitions =
  case
    [ (endpoint, keys)
    | (endpoint, keys) <- Map.toAscList consumers
    , Set.size keys > 1
    ] of
    [] -> Right ()
    (endpoint, keys) : _ -> Left (ProtocolEndpointConsumedMoreThanOnce endpoint keys)
  where
    consumers = Map.fromListWith Set.union
      [ (protocolTransitionPredecessor transition, Set.singleton key)
      | (key, transition) <- Map.toAscList transitions
      ]

checkEndpointProduction
  :: Map ProtocolTransitionKey ProtocolTransitionBinding
  -> Either ProtocolStateVerificationError ()
checkEndpointProduction transitions =
  case
    [ (endpoint, keys)
    | (endpoint, keys) <- Map.toAscList producers
    , Set.size keys > 1
    ] of
    [] -> Right ()
    (endpoint, keys) : _ -> Left (ProtocolEndpointProducedMoreThanOnce endpoint keys)
  where
    producers = Map.fromListWith Set.union
      [ (successor, Set.singleton key)
      | (key, transition) <- Map.toAscList transitions
      , ProtocolSuccessor successor <- Map.elems (protocolTransitionOutcomes transition)
      ]

checkAcyclicLineage
  :: Map EndpointOccurrenceKey ProtocolEndpointState
  -> Map ProtocolTransitionKey ProtocolTransitionBinding
  -> Either ProtocolStateVerificationError ()
checkAcyclicLineage endpoints transitions =
  case topologicalRemainder nodes edges of
    [] -> Right ()
    endpoint : _ -> Left (ProtocolEndpointLineageCycle endpoint)
  where
    nodes = Map.keysSet endpoints
    edges = Map.fromListWith Set.union
      [ (protocolTransitionPredecessor transition, Set.singleton successor)
      | transition <- Map.elems transitions
      , ProtocolSuccessor successor <- Map.elems (protocolTransitionOutcomes transition)
      ]

topologicalRemainder
  :: Set EndpointOccurrenceKey
  -> Map EndpointOccurrenceKey (Set EndpointOccurrenceKey)
  -> [EndpointOccurrenceKey]
topologicalRemainder nodes edges =
  go initialIndegree initialZero
  where
    initialIndegree = Set.foldl' (\acc node -> Map.insert node 0 acc) Map.empty nodes
    indegree = Map.foldlWithKey' addEdges initialIndegree edges
    addEdges acc _ successors = Set.foldl' (\m successor -> Map.insertWith (+) successor 1 m) acc successors
    initialZero = [node | (node, degree) <- Map.toAscList indegree, degree == 0]

    go current [] = [node | (node, degree) <- Map.toAscList current, degree > 0]
    go current (node : queue) =
      let successors = Map.findWithDefault Set.empty node edges
          (next, newlyZero) = Set.foldl' decrement (Map.delete node current, []) successors
      in go next (queue <> reverse newlyZero)

    decrement (current, newlyZero) successor =
      case Map.lookup successor current of
        Nothing -> (current, newlyZero)
        Just degree ->
          let degree' = degree - 1
              current' = Map.insert successor degree' current
          in if degree' == 0
              then (current', successor : newlyZero)
              else (current', newlyZero)

lookupFunction
  :: ProtocolTransitionKey
  -> Text
  -> SystemsProgram
  -> Either ProtocolStateVerificationError SystemsFunction
lookupFunction key name program = maybe
  (Left (ProtocolTransitionUnknownFunction key name))
  Right
  (Map.lookup name (systemsProgramFunctions program))

lookupBlock
  :: ProtocolTransitionKey
  -> BlockId
  -> SystemsFunction
  -> Either ProtocolStateVerificationError SystemsBlock
lookupBlock key blockId function = maybe
  (Left (ProtocolTransitionUnknownBlock key blockId))
  Right
  (Map.lookup blockId (systemsFunctionBlocks function))

protocolStageArtifact :: ControlStateStageBundle -> SystemsArtifact
protocolStageArtifact =
  phase1StageSystemsArtifact
    . subjectStageBase
    . providerCallStageBase
    . authorityEffectStageBase
    . branchResourceStageBase
    . controlStateStageBase

indexMaybe :: Int -> [a] -> Maybe a
indexMaybe index values
  | index < 0 = Nothing
  | otherwise = case drop index values of
      value : _ -> Just value
      [] -> Nothing

targetSiteFunction :: ProtocolTargetSite -> Text
targetSiteFunction site = case site of
  ProtocolOperationSite functionName _ _ -> functionName
  ProtocolTerminatorSite functionName _ -> functionName

semanticEndpoint :: ProtocolEndpointState -> SemanticForm
semanticEndpoint endpoint = SemanticRecord (Map.fromList
  [ ("occurrence", SemanticAtom
      (unEndpointOccurrenceKey (protocolEndpointOccurrence endpoint)))
  , ("instance", SemanticAtom
      (unProtocolInstanceRevision (protocolEndpointInstance endpoint)))
  , ("role", SemanticAtom (unProtocolRoleKey (protocolEndpointRole endpoint)))
  , ("session", SemanticAtom
      (unLocalSessionRevision (protocolEndpointSession endpoint)))
  ])

semanticTransition :: ProtocolTransitionBinding -> SemanticForm
semanticTransition transition = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (unProtocolTransitionKey (protocolTransitionKey transition)))
  , ("predecessor", SemanticAtom
      (unEndpointOccurrenceKey (protocolTransitionPredecessor transition)))
  , ("action", semanticAction (protocolTransitionAction transition))
  , ("target_site", semanticTargetSite (protocolTransitionTargetSite transition))
  , ("transport", semanticValueRef (protocolTransitionTransport transition))
  , ("outcomes", SemanticRecord (Map.fromList
      [ (label, semanticOutcome outcome)
      | (label, outcome) <- Map.toAscList (protocolTransitionOutcomes transition)
      ]))
  , ("basis", semanticBasis (protocolTransitionBasis transition))
  ])

semanticAction :: ProtocolAction -> SemanticForm
semanticAction action = case action of
  ProtocolReceiveCommit message -> tagged "receive-commit" message
  ProtocolSelect label -> tagged "select" label
  ProtocolOffer labels -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "offer")
    , ("labels", SemanticUnordered (Set.map SemanticAtom labels))
    ])
  ProtocolReceiveExact -> SemanticAtom "receive-exact"
  ProtocolSendExact -> SemanticAtom "send-exact"
  ProtocolOpaqueAction key -> tagged "opaque-action" key
  where
    tagged kind value = SemanticRecord (Map.fromList
      [("kind", SemanticAtom kind), ("value", SemanticAtom value)])

semanticTargetSite :: ProtocolTargetSite -> SemanticForm
semanticTargetSite site = case site of
  ProtocolOperationSite functionName blockId index -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "operation")
    , ("function", SemanticAtom functionName)
    , ("block", SemanticAtom (unBlockId blockId))
    , ("index", SemanticAtom (Text.pack (show index)))
    ])
  ProtocolTerminatorSite functionName blockId -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "terminator")
    , ("function", SemanticAtom functionName)
    , ("block", SemanticAtom (unBlockId blockId))
    ])

semanticValueRef :: SystemsValueRef -> SemanticForm
semanticValueRef ref = SemanticRecord (Map.fromList
  [ ("function", SemanticAtom (systemsValueRefFunction ref))
  , ("value", SemanticAtom (unValueId (systemsValueRefValue ref)))
  ])

semanticOutcome :: ProtocolTransitionOutcome -> SemanticForm
semanticOutcome outcome = case outcome of
  ProtocolSuccessor successor -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "successor")
    , ("occurrence", SemanticAtom (unEndpointOccurrenceKey successor))
    ])
  ProtocolTerminal reason -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "terminal")
    , ("reason", SemanticAtom reason)
    ])

semanticBasis :: ProtocolCorrespondenceBasis -> SemanticForm
semanticBasis basis = case basis of
  CheckedProtocolCorrespondence revision -> tagged "checked" revision
  CheckedLegacyOpaqueProtocolBridge evidence -> tagged "legacy-opaque-bridge" evidence
  RuntimeTransportCoincidence reason -> tagged "runtime-coincidence" reason
  where
    tagged kind value = SemanticRecord (Map.fromList
      [("kind", SemanticAtom kind), ("value", SemanticAtom value)])

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
