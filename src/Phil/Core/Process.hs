{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Process
  ( FlowPath
  , ProcessFlow
  , ProcessError (..)
  , flowPaths
  , pathControl
  , pathState
  , continueFlow
  , returnFlow
  , closedFlow
  , failedFlow
  , sequenceFlow
  , joinBranches
  , ProcessSiteKey (..)
  , ProcessKey (..)
  , ProcessDeclarationSite (..)
  , ActivationStatus (..)
  , ProcessOccurrence (..)
  , ProcessNetwork (..)
  , ProcessNetworkError (..)
  , deriveProcessKey
  , elaborateProcessNetwork
  , activateRootProcesses
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , ensureComplete
  , joinContinuing
  )
import Phil.Core.Static
  ( ArchitectureInstanceGraph (..)
  , ArchitectureInstanceIdentity (..)
  , CheckedArchitectureInstance (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Core.Syntax (Control (..), Outcome, Ty)

data FlowPath = FlowPath
  { pathControl :: Control
  , pathState :: CheckState
  }
  deriving (Eq, Show)

newtype ProcessFlow = ProcessFlow
  { unProcessFlow :: [FlowPath]
  }
  deriving (Eq, Show)

data ProcessError
  = InvalidReturnState CheckError
  | InvalidTerminalState Control CheckError
  | BranchJoinError CheckError
  | EmptyBranchSet
  deriving (Eq, Show)

flowPaths :: ProcessFlow -> [FlowPath]
flowPaths = unProcessFlow

continueFlow :: CheckState -> ProcessFlow
continueFlow state = ProcessFlow [FlowPath Continue state]

returnFlow :: Ty -> CheckState -> Either ProcessError ProcessFlow
returnFlow returnTy state = do
  ensureReturnable state
  pure (ProcessFlow [FlowPath (Return returnTy) state])

closedFlow :: Outcome -> CheckState -> Either ProcessError ProcessFlow
closedFlow outcome = terminalFlow (Closed outcome)

failedFlow :: Text -> Text -> CheckState -> Either ProcessError ProcessFlow
failedFlow failureClass detail = terminalFlow (Failed failureClass detail)

sequenceFlow
  :: ProcessFlow
  -> (CheckState -> Either err ProcessFlow)
  -> Either err ProcessFlow
sequenceFlow (ProcessFlow paths) continuation =
  ProcessFlow . concat <$> mapM advance paths
  where
    advance path =
      case pathControl path of
        Continue -> unProcessFlow <$> continuation (pathState path)
        Return _ -> pure [path]
        Closed _ -> pure [path]
        Failed _ _ -> pure [path]

joinBranches :: [ProcessFlow] -> Either ProcessError ProcessFlow
joinBranches [] = Left EmptyBranchSet
joinBranches flows = do
  let paths = concatMap unProcessFlow flows
      continuingPaths = filter ((== Continue) . pathControl) paths
  joinedContext <-
    case continuingPaths of
      [] -> pure Nothing
      _ -> Just <$> mapLeft BranchJoinError
        (joinContinuing (map (resourceContext . pathState) continuingPaths))
  pure (ProcessFlow (map (normalizeContinue joinedContext) paths))

normalizeContinue :: Maybe ResourceContext -> FlowPath -> FlowPath
normalizeContinue joinedContext path =
  case (pathControl path, joinedContext) of
    (Continue, Just context) ->
      path
        { pathState = (pathState path)
            { resourceContext = context
            }
        }
    _ -> path

terminalFlow :: Control -> CheckState -> Either ProcessError ProcessFlow
terminalFlow control state =
  case ensureComplete (resourceContext state) of
    Left err -> Left (InvalidTerminalState control err)
    Right () -> Right (ProcessFlow [FlowPath control state])

ensureReturnable :: CheckState -> Either ProcessError ()
ensureReturnable state
  | Set.null loans = Right ()
  | otherwise = Left (InvalidReturnState (EscapingLoans loans))
  where
    loans = sharedLoans (resourceContext state)

newtype ProcessSiteKey = ProcessSiteKey { unProcessSiteKey :: Text }
  deriving (Eq, Ord, Show)

newtype ProcessKey = ProcessKey { unProcessKey :: Text }
  deriving (Eq, Ord, Show)

data ProcessDeclarationSite = ProcessDeclarationSite
  { processSiteKey :: ProcessSiteKey
  , processTargetInstance :: InstanceKey
  }
  deriving (Eq, Ord, Show)

data ActivationStatus
  = NotActivated
  | Active
  deriving (Eq, Ord, Show)

data ProcessOccurrence = ProcessOccurrence
  { processOccurrenceKey :: ProcessKey
  , processOccurrenceRootRevision :: InstanceRevision
  , processOccurrenceTarget :: ArchitectureInstanceIdentity
  , processOccurrenceActivation :: ActivationStatus
  }
  deriving (Eq, Ord, Show)

data ProcessNetwork = ProcessNetwork
  { processNetworkRoot :: ArchitectureInstanceIdentity
  , processNetworkPopulation :: Map.Map ProcessKey ProcessOccurrence
  }
  deriving (Eq, Show)

data ProcessNetworkError
  = DuplicateProcessSiteKey ProcessSiteKey
  | UnknownProcessTarget ProcessSiteKey InstanceKey
  | DuplicateProcessKey ProcessKey
  | ProcessAlreadyActivated ProcessKey
  deriving (Eq, Show)

deriveProcessKey :: InstanceRevision -> ProcessSiteKey -> ProcessKey
deriveProcessKey rootRevision siteKey = ProcessKey
  ("phil.process.scope.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("root_revision", SemanticAtom (unInstanceRevision rootRevision))
      , ("site", SemanticAtom (unProcessSiteKey siteKey))
      ])))

elaborateProcessNetwork
  :: ArchitectureInstanceGraph
  -> [ProcessDeclarationSite]
  -> Either ProcessNetworkError ProcessNetwork
elaborateProcessNetwork graph sites = do
  uniqueSites <- normalizeSites sites
  population <- Map.foldlWithKey' addSite (Right Map.empty) uniqueSites
  Right ProcessNetwork
    { processNetworkRoot = architectureGraphRoot graph
    , processNetworkPopulation = population
    }
  where
    rootRevision = identityInstanceRevision (architectureGraphRoot graph)

    addSite accumulated siteKey targetKey = do
      current <- accumulated
      targetNode <- maybe
        (Left (UnknownProcessTarget siteKey targetKey))
        Right
        (Map.lookup targetKey (architectureGraphInstances graph))
      let key = deriveProcessKey rootRevision siteKey
          occurrence = ProcessOccurrence
            { processOccurrenceKey = key
            , processOccurrenceRootRevision = rootRevision
            , processOccurrenceTarget = checkedArchitectureIdentity targetNode
            , processOccurrenceActivation = NotActivated
            }
      if Map.member key current
        then Left (DuplicateProcessKey key)
        else Right (Map.insert key occurrence current)

normalizeSites
  :: [ProcessDeclarationSite]
  -> Either ProcessNetworkError (Map.Map ProcessSiteKey InstanceKey)
normalizeSites = go Set.empty Map.empty
  where
    go _ normalized [] = Right normalized
    go seen normalized (site : rest)
      | Set.member (processSiteKey site) seen =
          Left (DuplicateProcessSiteKey (processSiteKey site))
      | otherwise = go
          (Set.insert (processSiteKey site) seen)
          (Map.insert (processSiteKey site) (processTargetInstance site) normalized)
          rest

activateRootProcesses :: ProcessNetwork -> Either ProcessNetworkError ProcessNetwork
activateRootProcesses network = do
  activated <- Map.traverseWithKey activateOne (processNetworkPopulation network)
  Right network { processNetworkPopulation = activated }
  where
    activateOne key occurrence =
      case processOccurrenceActivation occurrence of
        NotActivated -> Right occurrence { processOccurrenceActivation = Active }
        Active -> Left (ProcessAlreadyActivated key)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
