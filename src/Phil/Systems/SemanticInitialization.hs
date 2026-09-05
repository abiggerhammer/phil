{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.SemanticInitialization
  ( SemanticStorageKey (..)
  , SemanticInitializationOrigin (..)
  , SemanticObservationKind (..)
  , SemanticInitializationEvent (..)
  , SemanticInitializationTrace (..)
  , CheckedSemanticInitializationTrace (..)
  , SemanticInitializationError (..)
  , renderSemanticInitializationTrace
  , checkSemanticInitializationTrace
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest)
import Phil.Systems.IR
  ( StageContract (..)
  , ValueId (..)
  )

-- | Exact semantic identity of reserved realization storage.  This is not a
-- target pointer, stack slot, register number, or other physical identity.
newtype SemanticStorageKey = SemanticStorageKey
  { unSemanticStorageKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Admitted ways in which a Phil semantic value may first become available.
-- The origin class is explicit so target storage reservation cannot silently
-- masquerade as source-level initialization.
data SemanticInitializationOrigin
  = SemanticRootInput
  | SemanticLiteralValue
  | SemanticConstructedValue
  | SemanticPatternValue
  | SemanticCallableResult
  | SemanticProviderResult
  | SemanticProtocolSuccessor
  | SemanticResourceSuccessor
  | SemanticBoundaryValue
  deriving (Eq, Ord, Show)

-- | Source-significant observations that require an already-established Phil
-- semantic value.  Merely having bytes/storage at the target is insufficient.
data SemanticObservationKind
  = SemanticRead
  | SemanticCompare
  | SemanticSerialize
  | SemanticHash
  | SemanticEvidenceUse
  | SemanticExport
  deriving (Eq, Ord, Show)

data SemanticInitializationEvent
  = SemanticStorageReserved SemanticStorageKey
  | SemanticValueInitialized
      ValueId
      (Maybe SemanticStorageKey)
      SemanticInitializationOrigin
  | SemanticValueObserved ValueId SemanticObservationKind
  deriving (Eq, Ord, Show)

-- | Ordered initialization/observation relation for one exact StageContract.
-- StageContract.trace_relation remains a set-like bag of relation facts; the
-- event order is encoded inside this exact content-bearing witness.
data SemanticInitializationTrace = SemanticInitializationTrace
  { semanticInitializationStageContractId :: Text
  , semanticInitializationSourceDigest :: Digest
  , semanticInitializationTargetDigest :: Digest
  , semanticInitializationEvents :: [SemanticInitializationEvent]
  }
  deriving (Eq, Show)

data CheckedSemanticInitializationTrace = CheckedSemanticInitializationTrace
  { checkedSemanticInitializedValues :: Set.Set ValueId
  , checkedSemanticReservedStorage :: Set.Set SemanticStorageKey
  }
  deriving (Eq, Show)

data SemanticInitializationError
  = SemanticInitializationStageContractIdMismatch Text Text
  | SemanticInitializationSourceDigestMismatch Digest Digest
  | SemanticInitializationTargetDigestMismatch Digest Digest
  | SemanticInitializationMissingTraceRelation Text
  | SemanticInitializationEmptyStorageKey
  | SemanticStorageReservedTwice SemanticStorageKey
  | SemanticInitializationStorageNotReserved ValueId SemanticStorageKey
  | SemanticValueReinitialized ValueId
  | SemanticObservationBeforeInitialization ValueId SemanticObservationKind
  deriving (Eq, Show)

renderSemanticInitializationTrace :: SemanticInitializationTrace -> Text
renderSemanticInitializationTrace trace = Text.intercalate "|"
  [ "phil.exec.initialization.v1"
  , "events=" <> Text.intercalate "," (map renderEvent (semanticInitializationEvents trace))
  ]

checkSemanticInitializationTrace
  :: StageContract
  -> SemanticInitializationTrace
  -> Either SemanticInitializationError CheckedSemanticInitializationTrace
checkSemanticInitializationTrace contract trace = do
  if semanticInitializationStageContractId trace == stageContractId contract
    then Right ()
    else Left
      (SemanticInitializationStageContractIdMismatch
        (stageContractId contract)
        (semanticInitializationStageContractId trace))
  if semanticInitializationSourceDigest trace == stageSourceArtifactDigest contract
    then Right ()
    else Left
      (SemanticInitializationSourceDigestMismatch
        (stageSourceArtifactDigest contract)
        (semanticInitializationSourceDigest trace))
  if semanticInitializationTargetDigest trace == stageTargetArtifactDigest contract
    then Right ()
    else Left
      (SemanticInitializationTargetDigestMismatch
        (stageTargetArtifactDigest contract)
        (semanticInitializationTargetDigest trace))
  let relation = renderSemanticInitializationTrace trace
  if relation `elem` stageTraceRelation contract
    then Right ()
    else Left (SemanticInitializationMissingTraceRelation relation)
  final <- foldl checkEvent (Right emptyState) (semanticInitializationEvents trace)
  Right CheckedSemanticInitializationTrace
    { checkedSemanticInitializedValues = Map.keysSet (initializationValues final)
    , checkedSemanticReservedStorage = initializationStorage final
    }

-- Internal state intentionally records only semantic identities and admitted
-- initialization facts.  Target contents are never consulted.
data InitializationState = InitializationState
  { initializationStorage :: Set.Set SemanticStorageKey
  , initializationValues :: Map.Map ValueId SemanticInitializationOrigin
  }

emptyState :: InitializationState
emptyState = InitializationState Set.empty Map.empty

checkEvent
  :: Either SemanticInitializationError InitializationState
  -> SemanticInitializationEvent
  -> Either SemanticInitializationError InitializationState
checkEvent accumulated event = do
  state <- accumulated
  case event of
    SemanticStorageReserved storage -> do
      if Text.null (unSemanticStorageKey storage)
        then Left SemanticInitializationEmptyStorageKey
        else Right ()
      if Set.member storage (initializationStorage state)
        then Left (SemanticStorageReservedTwice storage)
        else Right state
          { initializationStorage = Set.insert storage (initializationStorage state)
          }
    SemanticValueInitialized value maybeStorage origin -> do
      case Map.lookup value (initializationValues state) of
        Just _ -> Left (SemanticValueReinitialized value)
        Nothing -> Right ()
      case maybeStorage of
        Nothing -> Right ()
        Just storage ->
          if Set.member storage (initializationStorage state)
            then Right ()
            else Left (SemanticInitializationStorageNotReserved value storage)
      Right state
        { initializationValues = Map.insert value origin (initializationValues state)
        }
    SemanticValueObserved value observation ->
      if Map.member value (initializationValues state)
        then Right state
        else Left (SemanticObservationBeforeInitialization value observation)

renderEvent :: SemanticInitializationEvent -> Text
renderEvent event = case event of
  SemanticStorageReserved storage ->
    "reserve(" <> unSemanticStorageKey storage <> ")"
  SemanticValueInitialized value maybeStorage origin -> Text.intercalate ":"
    [ "init"
    , renderValue value
    , maybe "none" unSemanticStorageKey maybeStorage
    , renderOrigin origin
    ]
  SemanticValueObserved value observation -> Text.intercalate ":"
    [ "observe"
    , renderValue value
    , renderObservation observation
    ]

renderValue :: ValueId -> Text
renderValue = unValueId

renderOrigin :: SemanticInitializationOrigin -> Text
renderOrigin origin = case origin of
  SemanticRootInput -> "root"
  SemanticLiteralValue -> "literal"
  SemanticConstructedValue -> "constructor"
  SemanticPatternValue -> "pattern"
  SemanticCallableResult -> "callable-result"
  SemanticProviderResult -> "provider-result"
  SemanticProtocolSuccessor -> "protocol-successor"
  SemanticResourceSuccessor -> "resource-successor"
  SemanticBoundaryValue -> "boundary"

renderObservation :: SemanticObservationKind -> Text
renderObservation observation = case observation of
  SemanticRead -> "read"
  SemanticCompare -> "compare"
  SemanticSerialize -> "serialize"
  SemanticHash -> "hash"
  SemanticEvidenceUse -> "evidence"
  SemanticExport -> "export"
