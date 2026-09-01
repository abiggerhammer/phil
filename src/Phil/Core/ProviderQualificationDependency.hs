{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderQualificationDependency
  ( QualificationGroundKey (..)
  , QualificationGroundKind (..)
  , QualificationGroundDisposition (..)
  , QualificationGround (..)
  , ProviderQualificationDependencyNode (..)
  , ProviderQualificationDependencyGraph (..)
  , CheckedProviderQualificationDependencyGraph (..)
  , ProviderQualificationDependencyError (..)
  , checkProviderQualificationDependencyGraph
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualificationIdentity
  ( ProviderQualificationAdmissionDecision (..)
  , QualificationAdmissionRevision
  )
import ProviderQualificationLineageCoreKernel
  ( QualificationDependencyClosureDecision (..)
  , QualificationDependencyNodeDecision (..)
  , QualificationRegistryDecision (..)
  , QualificationRootDecision (..)
  , decideQualificationDependencyClosureByFacts
  , decideQualificationDependencyNodeByFacts
  , decideQualificationRegistryByFacts
  , decideQualificationRootByFacts
  , propagateGroundPresence
  )

newtype QualificationGroundKey = QualificationGroundKey
  { unQualificationGroundKey :: Text
  }
  deriving (Eq, Ord, Show)

data QualificationGroundKind
  = ProofGround
  | RuntimeEnforcementGround
  | ExternalEvidenceGround
  | AssumptionGround
  | TrustedComputingBaseGround
  deriving (Eq, Ord, Show)

data QualificationGroundDisposition
  = QualificationGroundAccepted
  | QualificationGroundRejected (Set.Set Text)
  deriving (Eq, Ord, Show)

-- | One independently evaluated grounding fact. An accepted assumption or TCB
-- boundary is still conditional grounding rather than proof of the environment;
-- the important property here is that it does not derive its validity from the
-- provider qualifications being closed by this graph.
data QualificationGround = QualificationGround
  { qualificationGroundKey :: QualificationGroundKey
  , qualificationGroundKind :: QualificationGroundKind
  , qualificationGroundRevision :: Text
  , qualificationGroundValidityScope :: Text
  , qualificationGroundDisposition :: QualificationGroundDisposition
  }
  deriving (Eq, Ord, Show)

-- | Dependency facts for one exact provider admission revision. Dependencies on
-- other admissions are allowed, but they do not independently ground this node.
-- Ground references are the only leaves in this bounded closure graph.
data ProviderQualificationDependencyNode = ProviderQualificationDependencyNode
  { qualificationDependencyAdmissionRevision :: QualificationAdmissionRevision
  , qualificationDependencyAdmissionDecision :: ProviderQualificationAdmissionDecision
  , qualificationDependencyAdmissions :: Set.Set QualificationAdmissionRevision
  , qualificationDependencyGrounds :: Set.Set QualificationGroundKey
  }
  deriving (Eq, Ord, Show)

data ProviderQualificationDependencyGraph = ProviderQualificationDependencyGraph
  { qualificationDependencyRoots :: Set.Set QualificationAdmissionRevision
  , qualificationDependencyNodes
      :: Map.Map QualificationAdmissionRevision ProviderQualificationDependencyNode
  , qualificationDependencyGroundRegistry
      :: Map.Map QualificationGroundKey QualificationGround
  }
  deriving (Eq, Ord, Show)

data CheckedProviderQualificationDependencyGraph =
  CheckedProviderQualificationDependencyGraph
    { checkedQualificationDependencyRoots :: Set.Set QualificationAdmissionRevision
    , checkedQualificationDependencyGroundsByAdmission
        :: Map.Map QualificationAdmissionRevision (Set.Set QualificationGroundKey)
    , checkedQualificationDependencyGroundRegistry
        :: Map.Map QualificationGroundKey QualificationGround
    }
  deriving (Eq, Ord, Show)

data ProviderQualificationDependencyError
  = QualificationDependencyNodeKeyMismatch
      QualificationAdmissionRevision QualificationAdmissionRevision
  | QualificationGroundRegistryKeyMismatch
      QualificationGroundKey QualificationGroundKey
  | QualificationDependencyUnknownRoot QualificationAdmissionRevision
  | QualificationDependencyUnknownAdmission
      QualificationAdmissionRevision QualificationAdmissionRevision
  | QualificationDependencyUnknownGround
      QualificationAdmissionRevision QualificationGroundKey
  | QualificationDependencyRejectedAdmission
      QualificationAdmissionRevision (Set.Set Text)
  | QualificationDependencyRejectedGround
      QualificationAdmissionRevision QualificationGroundKey (Set.Set Text)
  | QualificationDependencyUngrounded
      (Set.Set QualificationAdmissionRevision)
  deriving (Eq, Ord, Show)

-- | Close the PROV-012 dependency graph. Qualification-to-qualification edges
-- may form cycles, but every node reachable from a selected root must eventually
-- inherit at least one independently accepted ground. A cycle that only points
-- to itself/its peers therefore remains empty under the least fixed point and is
-- rejected as circular self-endorsement.
checkProviderQualificationDependencyGraph
  :: ProviderQualificationDependencyGraph
  -> Either ProviderQualificationDependencyError CheckedProviderQualificationDependencyGraph
checkProviderQualificationDependencyGraph graph = do
  validateRegistryKeys
  validateRoots
  validateReachableNodes
  let reachable = reachableAdmissions
      initialGrounds = Map.fromSet directAcceptedGrounds reachable
      closedGrounds = closeGrounds reachable initialGrounds
      ungrounded = Set.filter
        (maybe True Set.null . (`Map.lookup` closedGrounds)) reachable
  case decideQualificationDependencyClosureByFacts (Set.null ungrounded) of
    QualificationDependencyUngroundedDecision ->
      Left (QualificationDependencyUngrounded ungrounded)
    QualificationDependencyClosureAcceptedDecision ->
      Right CheckedProviderQualificationDependencyGraph
        { checkedQualificationDependencyRoots = qualificationDependencyRoots graph
        , checkedQualificationDependencyGroundsByAdmission = closedGrounds
        , checkedQualificationDependencyGroundRegistry =
            qualificationDependencyGroundRegistry graph
        }
  where
    nodes = qualificationDependencyNodes graph
    grounds = qualificationDependencyGroundRegistry graph
    groundUniverse = Map.keysSet grounds

    validateRegistryKeys = do
      mapM_ validateNodeKey (Map.toAscList nodes)
      mapM_ validateGroundKey (Map.toAscList grounds)

    validateNodeKey (key, node) =
      case decideQualificationRegistryByFacts
          (key == qualificationDependencyAdmissionRevision node) True of
        QualificationRegistryAcceptedDecision -> Right ()
        _ -> Left (QualificationDependencyNodeKeyMismatch
          key (qualificationDependencyAdmissionRevision node))

    validateGroundKey (key, ground) =
      case decideQualificationRegistryByFacts
          True (key == qualificationGroundKey ground) of
        QualificationRegistryAcceptedDecision -> Right ()
        _ -> Left (QualificationGroundRegistryKeyMismatch
          key (qualificationGroundKey ground))

    validateRoots = mapM_ validateRoot
      (Set.toAscList (qualificationDependencyRoots graph))

    validateRoot root =
      case decideQualificationRootByFacts (Map.member root nodes) of
        QualificationRootAcceptedDecision -> Right ()
        QualificationUnknownRootDecision ->
          Left (QualificationDependencyUnknownRoot root)

    validateReachableNodes = mapM_ validateReachable
      (Set.toAscList reachableAdmissions)

    validateReachable admission = case Map.lookup admission nodes of
      Nothing -> Right ()
      Just node -> validateNode node

    validateNode node = do
      let owner = qualificationDependencyAdmissionRevision node
          (admissionAccepted, rejectedReasons) =
            case qualificationDependencyAdmissionDecision node of
              QualificationAdmitted -> (True, Set.empty)
              QualificationRejected reasons -> (False, reasons)
      case decideQualificationDependencyNodeByFacts
          admissionAccepted True True True of
        QualificationDependencyNodeAcceptedDecision -> Right ()
        _ -> Left (QualificationDependencyRejectedAdmission owner rejectedReasons)
      mapM_ (validateAdmissionDependency owner)
        (Set.toAscList (qualificationDependencyAdmissions node))
      mapM_ (validateGroundDependency owner)
        (Set.toAscList (qualificationDependencyGrounds node))

    validateAdmissionDependency owner dependency =
      case decideQualificationDependencyNodeByFacts
          True (Map.member dependency nodes) True True of
        QualificationDependencyNodeAcceptedDecision -> Right ()
        _ -> Left (QualificationDependencyUnknownAdmission owner dependency)

    validateGroundDependency owner groundKey = case Map.lookup groundKey grounds of
      Nothing ->
        case decideQualificationDependencyNodeByFacts True True False True of
          QualificationDependencyNodeAcceptedDecision -> Right ()
          _ -> Left (QualificationDependencyUnknownGround owner groundKey)
      Just ground ->
        let (groundAccepted, rejectedReasons) =
              case qualificationGroundDisposition ground of
                QualificationGroundAccepted -> (True, Set.empty)
                QualificationGroundRejected reasons -> (False, reasons)
        in case decideQualificationDependencyNodeByFacts
            True True True groundAccepted of
          QualificationDependencyNodeAcceptedDecision -> Right ()
          _ -> Left (QualificationDependencyRejectedGround
            owner groundKey rejectedReasons)

    reachableAdmissions = go Set.empty
      (Set.toAscList (qualificationDependencyRoots graph))
      where
        go seen [] = seen
        go seen (current : rest)
          | Set.member current seen = go seen rest
          | otherwise = case Map.lookup current nodes of
              Nothing -> go (Set.insert current seen) rest
              Just node -> go
                (Set.insert current seen)
                (Set.toAscList (qualificationDependencyAdmissions node) <> rest)

    directAcceptedGrounds admission = case Map.lookup admission nodes of
      Nothing -> Set.empty
      Just node -> Set.filter isAcceptedGround (qualificationDependencyGrounds node)

    isAcceptedGround key = case Map.lookup key grounds of
      Just ground -> qualificationGroundDisposition ground == QualificationGroundAccepted
      Nothing -> False

    closeGrounds reachable current =
      let next = Set.foldl' (propagate reachable) current reachable
      in if next == current then current else closeGrounds reachable next

    propagate reachable accumulated admission = case Map.lookup admission nodes of
      Nothing -> accumulated
      Just node ->
        let own = Map.findWithDefault Set.empty admission accumulated
            dependencyGroundSets =
              [ Map.findWithDefault Set.empty dependency accumulated
              | dependency <- Set.toAscList (qualificationDependencyAdmissions node)
              , Set.member dependency reachable
              ]
            propagated = Set.filter
              (\groundKey -> propagateGroundPresence
                (Set.member groundKey own)
                [ Set.member groundKey dependencyGrounds
                | dependencyGrounds <- dependencyGroundSets
                ])
              groundUniverse
        in Map.insert admission propagated accumulated
