{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessCausality
  ( ProcessEventKey (..)
  , ProcessEventKind (..)
  , ProcessEvent (..)
  , ArchitectureCausalEdge (..)
  , CausalEdgeOrigin (..)
  , CausalEdge (..)
  , ProcessPartialOrder (..)
  , ProcessCausalityError (..)
  , buildProcessPartialOrder
  , orderedBefore
  , incomparableEvents
  , validateEventLinearization
  ) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Process (ProcessKey)

newtype ProcessEventKey = ProcessEventKey { unProcessEventKey :: Text }
  deriving (Eq, Ord, Show)

data ProcessEventKind
  = LocalProcessEvent ProcessKey
  | SynchronousRendezvousEvent ProcessKey ProcessKey
  deriving (Eq, Ord, Show)

data ProcessEvent = ProcessEvent
  { processEventKey :: ProcessEventKey
  , processEventKind :: ProcessEventKind
  }
  deriving (Eq, Ord, Show)

data ArchitectureCausalEdge = ArchitectureCausalEdge
  { architectureCausalLabel :: Text
  , architectureCausalBefore :: ProcessEventKey
  , architectureCausalAfter :: ProcessEventKey
  }
  deriving (Eq, Ord, Show)

data CausalEdgeOrigin
  = LocalProgramOrder ProcessKey
  | SynchronousCommunicationOrder ProcessKey ProcessEventKey
  | ExplicitArchitectureCausality Text
  deriving (Eq, Ord, Show)

data CausalEdge = CausalEdge
  { causalBefore :: ProcessEventKey
  , causalAfter :: ProcessEventKey
  , causalOrigin :: CausalEdgeOrigin
  }
  deriving (Eq, Ord, Show)

data ProcessPartialOrder = ProcessPartialOrder
  { partialOrderEvents :: Map.Map ProcessEventKey ProcessEvent
  , partialOrderEdges :: Set.Set CausalEdge
  }
  deriving (Eq, Show)

data ProcessCausalityError
  = DuplicateProcessEvent ProcessEventKey
  | DuplicateProcessSequence ProcessKey
  | UnknownSequenceEvent ProcessKey ProcessEventKey
  | EventNotInProcess ProcessKey ProcessEventKey
  | MissingProcessSequence ProcessKey ProcessEventKey
  | UnknownArchitectureEdgeEndpoint ProcessEventKey
  | SelfCausalEdge ProcessEventKey CausalEdgeOrigin
  | CyclicProcessCausality ProcessEventKey ProcessEventKey
  | LinearizationDuplicateEvent ProcessEventKey
  | LinearizationEventSetMismatch
      (Set.Set ProcessEventKey)
      (Set.Set ProcessEventKey)
  | LinearizationViolatesCausality CausalEdge
  deriving (Eq, Show)

buildProcessPartialOrder
  :: [ProcessEvent]
  -> [(ProcessKey, [ProcessEventKey])]
  -> [ArchitectureCausalEdge]
  -> Either ProcessCausalityError ProcessPartialOrder
buildProcessPartialOrder eventEntries sequenceEntries architectureEdges = do
  events <- normalizeEvents eventEntries
  sequences <- normalizeSequences sequenceEntries
  validateSequenceMembership events sequences
  localEdges <- deriveSequenceEdges events sequences
  explicitEdges <- mapM (validateArchitectureEdge events) architectureEdges
  let edges = Set.fromList (localEdges <> explicitEdges)
      order = ProcessPartialOrder events edges
  validateAcyclic order
  pure order

normalizeEvents
  :: [ProcessEvent]
  -> Either ProcessCausalityError (Map.Map ProcessEventKey ProcessEvent)
normalizeEvents = foldl' insertOne (Right Map.empty)
  where
    insertOne accumulated event = do
      current <- accumulated
      let key = processEventKey event
      if Map.member key current
        then Left (DuplicateProcessEvent key)
        else Right (Map.insert key event current)

normalizeSequences
  :: [(ProcessKey, [ProcessEventKey])]
  -> Either ProcessCausalityError (Map.Map ProcessKey [ProcessEventKey])
normalizeSequences = foldl' insertOne (Right Map.empty)
  where
    insertOne accumulated (processKey, events) = do
      current <- accumulated
      if Map.member processKey current
        then Left (DuplicateProcessSequence processKey)
        else Right (Map.insert processKey events current)

validateSequenceMembership
  :: Map.Map ProcessEventKey ProcessEvent
  -> Map.Map ProcessKey [ProcessEventKey]
  -> Either ProcessCausalityError ()
validateSequenceMembership events sequences = do
  mapM_ validateOneSequence (Map.toList sequences)
  mapM_ requireParticipantSequence (Map.elems events)
  where
    validateOneSequence (processKey, eventKeys) =
      mapM_ (validateOne processKey) eventKeys

    validateOne processKey eventKey = do
      event <- maybe
        (Left (UnknownSequenceEvent processKey eventKey))
        Right
        (Map.lookup eventKey events)
      if Set.member processKey (eventParticipants event)
        then Right ()
        else Left (EventNotInProcess processKey eventKey)

    requireParticipantSequence event =
      mapM_ (requireInSequence (processEventKey event))
        (Set.toList (eventParticipants event))

    requireInSequence eventKey processKey =
      case Map.lookup processKey sequences of
        Nothing -> Left (MissingProcessSequence processKey eventKey)
        Just keys
          | eventKey `elem` keys -> Right ()
          | otherwise -> Left (MissingProcessSequence processKey eventKey)

deriveSequenceEdges
  :: Map.Map ProcessEventKey ProcessEvent
  -> Map.Map ProcessKey [ProcessEventKey]
  -> Either ProcessCausalityError [CausalEdge]
deriveSequenceEdges events sequences =
  concat <$> mapM deriveOne (Map.toList sequences)
  where
    deriveOne (processKey, keys) =
      mapM (mkEdge processKey) (zip keys (drop 1 keys))

    mkEdge processKey (before, after) = do
      beforeEvent <- requireEvent before
      afterEvent <- requireEvent after
      let origin = sequenceEdgeOrigin processKey beforeEvent afterEvent
      if before == after
        then Left (SelfCausalEdge before origin)
        else Right CausalEdge
          { causalBefore = before
          , causalAfter = after
          , causalOrigin = origin
          }

    requireEvent key = maybe
      (Left (UnknownSequenceEvent (error "validated process sequence") key))
      Right
      (Map.lookup key events)

sequenceEdgeOrigin :: ProcessKey -> ProcessEvent -> ProcessEvent -> CausalEdgeOrigin
sequenceEdgeOrigin processKey before after =
  case rendezvousKey before of
    Just key -> SynchronousCommunicationOrder processKey key
    Nothing -> case rendezvousKey after of
      Just key -> SynchronousCommunicationOrder processKey key
      Nothing -> LocalProgramOrder processKey

rendezvousKey :: ProcessEvent -> Maybe ProcessEventKey
rendezvousKey event =
  case processEventKind event of
    SynchronousRendezvousEvent _ _ -> Just (processEventKey event)
    LocalProcessEvent _ -> Nothing

validateArchitectureEdge
  :: Map.Map ProcessEventKey ProcessEvent
  -> ArchitectureCausalEdge
  -> Either ProcessCausalityError CausalEdge
validateArchitectureEdge events edge = do
  requireKnown (architectureCausalBefore edge)
  requireKnown (architectureCausalAfter edge)
  let origin = ExplicitArchitectureCausality (architectureCausalLabel edge)
      before = architectureCausalBefore edge
      after = architectureCausalAfter edge
  if before == after
    then Left (SelfCausalEdge before origin)
    else Right CausalEdge
      { causalBefore = before
      , causalAfter = after
      , causalOrigin = origin
      }
  where
    requireKnown key
      | Map.member key events = Right ()
      | otherwise = Left (UnknownArchitectureEdgeEndpoint key)

eventParticipants :: ProcessEvent -> Set.Set ProcessKey
eventParticipants event =
  case processEventKind event of
    LocalProcessEvent processKey -> Set.singleton processKey
    SynchronousRendezvousEvent left right -> Set.fromList [left, right]

validateAcyclic :: ProcessPartialOrder -> Either ProcessCausalityError ()
validateAcyclic order =
  case
    [ (causalBefore edge, causalAfter edge)
    | edge <- Set.toList (partialOrderEdges order)
    , pathExists order (causalAfter edge) (causalBefore edge)
    ] of
      [] -> Right ()
      (before, after) : _ -> Left (CyclicProcessCausality before after)

orderedBefore :: ProcessPartialOrder -> ProcessEventKey -> ProcessEventKey -> Bool
orderedBefore order before after
  | before == after = False
  | otherwise = pathExists order before after

incomparableEvents :: ProcessPartialOrder -> ProcessEventKey -> ProcessEventKey -> Bool
incomparableEvents order left right =
  left /= right
    && not (orderedBefore order left right)
    && not (orderedBefore order right left)

pathExists :: ProcessPartialOrder -> ProcessEventKey -> ProcessEventKey -> Bool
pathExists order start target = go Set.empty [start]
  where
    adjacency = Map.fromListWith Set.union
      [ (causalBefore edge, Set.singleton (causalAfter edge))
      | edge <- Set.toList (partialOrderEdges order)
      ]

    go _ [] = False
    go seen (current : rest)
      | Set.member current seen = go seen rest
      | otherwise =
          let next = Set.toList (Map.findWithDefault Set.empty current adjacency)
          in target `elem` next
              || go (Set.insert current seen) (next <> rest)

validateEventLinearization
  :: ProcessPartialOrder
  -> [ProcessEventKey]
  -> Either ProcessCausalityError ()
validateEventLinearization order linearization = do
  ensureNoDuplicates Set.empty linearization
  let expected = Map.keysSet (partialOrderEvents order)
      actual = Set.fromList linearization
  if expected == actual
    then Right ()
    else Left (LinearizationEventSetMismatch expected actual)
  let positions = Map.fromList (zip linearization [0 :: Int ..])
  case filter (violated positions) (Set.toList (partialOrderEdges order)) of
    [] -> Right ()
    edge : _ -> Left (LinearizationViolatesCausality edge)
  where
    ensureNoDuplicates _ [] = Right ()
    ensureNoDuplicates seen (key : rest)
      | Set.member key seen = Left (LinearizationDuplicateEvent key)
      | otherwise = ensureNoDuplicates (Set.insert key seen) rest

    violated positions edge =
      case (Map.lookup (causalBefore edge) positions, Map.lookup (causalAfter edge) positions) of
        (Just beforePosition, Just afterPosition) -> beforePosition >= afterPosition
        _ -> False
