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
  , processSiteKey
  , processSiteOwningInstance
  , processTargetInstance
  , ActivationStatus (..)
  , ProcessOccurrence (..)
  , ProcessNetwork (..)
  , ProcessNetworkError (..)
  , deriveProcessKey
  , deriveScopedProcessKey
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

-- | The two-argument constructor is the root-architecture shorthand used by
-- the original CONC-001 implementation.  A process declaration instantiated
-- inside a nested architecture occurrence uses 'ScopedProcessDeclarationSite'
-- so the same declaration-local ProcessSiteKey can occur under distinct exact
-- owning InstanceKeys without becoming a global-name collision.
data ProcessDeclarationSite
  = ProcessDeclarationSite ProcessSiteKey InstanceKey
  | ScopedProcessDeclarationSite InstanceKey ProcessSiteKey InstanceKey
  deriving (Eq, Ord, Show)

processSiteKey :: ProcessDeclarationSite -> ProcessSiteKey
processSiteKey site = case site of
  ProcessDeclarationSite key _ -> key
  ScopedProcessDeclarationSite _ key _ -> key

processSiteOwningInstance :: ProcessDeclarationSite -> Maybe InstanceKey
processSiteOwningInstance site = case site of
  ProcessDeclarationSite _ _ -> Nothing
  ScopedProcessDeclarationSite owner _ _ -> Just owner

processTargetInstance :: ProcessDeclarationSite -> InstanceKey
processTargetInstance site = case site of
  ProcessDeclarationSite _ target -> target
  ScopedProcessDeclarationSite _ _ target -> target

data ActivationStatus
  = NotActivated
  | Active
  deriving (Eq, Ord, Show)

data ProcessOccurrence = ProcessOccurrence
  { processOccurrenceKey :: ProcessKey
  , processOccurrenceRootRevision :: InstanceRevision
  , processOccurrenceOwner :: ArchitectureInstanceIdentity
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
  | DuplicateScopedProcessSiteKey InstanceKey ProcessSiteKey
  | DuplicateProcessTarget InstanceKey ProcessSiteKey ProcessSiteKey
  | DuplicateScopedProcessTarget
      InstanceKey
      InstanceKey ProcessSiteKey
      InstanceKey ProcessSiteKey
  | UnknownProcessSiteOwner InstanceKey ProcessSiteKey
  | UnknownProcessTarget ProcessSiteKey InstanceKey
  | UnknownScopedProcessTarget InstanceKey ProcessSiteKey InstanceKey
  | DuplicateProcessKey ProcessKey
  | ProcessAlreadyActivated ProcessKey
  deriving (Eq, Show)

-- | Historical root-process key derivation.  Root sites continue to use the
-- exact existing rule so this bounded repair does not churn already-landed
-- ProcessKeys merely by introducing nested-instance competence.
deriveProcessKey :: InstanceRevision -> ProcessSiteKey -> ProcessKey
deriveProcessKey rootRevision siteKey = ProcessKey
  ("phil.process.scope.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("root_revision", SemanticAtom (unInstanceRevision rootRevision))
      , ("site", SemanticAtom (unProcessSiteKey siteKey))
      ])))

-- | Nested process-site identity is scoped by the stable owning architecture
-- occurrence.  The exact containing InstanceRevision remains available on the
-- checked ProcessOccurrence; it is not substituted for the generative owner
-- identity used to distinguish equal local sites in distinct occurrences.
deriveScopedProcessKey :: InstanceKey -> ProcessSiteKey -> ProcessKey
deriveScopedProcessKey ownerKey siteKey = ProcessKey
  ("phil.process.instance-scope.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("owner_instance", SemanticAtom (unInstanceKey ownerKey))
      , ("site", SemanticAtom (unProcessSiteKey siteKey))
      ])))

elaborateProcessNetwork
  :: ArchitectureInstanceGraph
  -> [ProcessDeclarationSite]
  -> Either ProcessNetworkError ProcessNetwork
elaborateProcessNetwork graph sites = do
  uniqueSites <- normalizeSites rootKey sites
  population <- Map.foldlWithKey' addSite (Right Map.empty) uniqueSites
  Right ProcessNetwork
    { processNetworkRoot = rootIdentity
    , processNetworkPopulation = population
    }
  where
    rootIdentity = architectureGraphRoot graph
    rootKey = identityInstanceKey rootIdentity
    rootRevision = identityInstanceRevision rootIdentity

    addSite accumulated (ownerKey, siteKey) targetKey = do
      current <- accumulated
      ownerNode <- maybe
        (Left (UnknownProcessSiteOwner ownerKey siteKey))
        Right
        (Map.lookup ownerKey (architectureGraphInstances graph))
      targetNode <- maybe
        (Left (unknownTarget ownerKey siteKey targetKey))
        Right
        (Map.lookup targetKey (architectureGraphInstances graph))
      let key
            | ownerKey == rootKey = deriveProcessKey rootRevision siteKey
            | otherwise = deriveScopedProcessKey ownerKey siteKey
          occurrence = ProcessOccurrence
            { processOccurrenceKey = key
            , processOccurrenceRootRevision = rootRevision
            , processOccurrenceOwner = checkedArchitectureIdentity ownerNode
            , processOccurrenceTarget = checkedArchitectureIdentity targetNode
            , processOccurrenceActivation = NotActivated
            }
      if Map.member key current
        then Left (DuplicateProcessKey key)
        else Right (Map.insert key occurrence current)

    unknownTarget ownerKey siteKey targetKey
      | ownerKey == rootKey = UnknownProcessTarget siteKey targetKey
      | otherwise = UnknownScopedProcessTarget ownerKey siteKey targetKey

normalizeSites
  :: InstanceKey
  -> [ProcessDeclarationSite]
  -> Either ProcessNetworkError (Map.Map (InstanceKey, ProcessSiteKey) InstanceKey)
normalizeSites rootKey = go Set.empty Map.empty Map.empty
  where
    go _ _ normalized [] = Right normalized
    go seenSites seenTargets normalized (site : rest)
      | Set.member address seenSites = Left (duplicateSiteError ownerKey siteKey)
      | Just previousAddress <- Map.lookup targetKey seenTargets =
          Left (duplicateTargetError targetKey previousAddress address)
      | otherwise = go
          (Set.insert address seenSites)
          (Map.insert targetKey address seenTargets)
          (Map.insert address targetKey normalized)
          rest
      where
        ownerKey = case processSiteOwningInstance site of
          Nothing -> rootKey
          Just owner -> owner
        siteKey = processSiteKey site
        targetKey = processTargetInstance site
        address = (ownerKey, siteKey)

    duplicateSiteError ownerKey siteKey
      | ownerKey == rootKey = DuplicateProcessSiteKey siteKey
      | otherwise = DuplicateScopedProcessSiteKey ownerKey siteKey

    duplicateTargetError targetKey (previousOwner, previousSite) (ownerKey, siteKey)
      | previousOwner == rootKey && ownerKey == rootKey =
          DuplicateProcessTarget targetKey previousSite siteKey
      | otherwise = DuplicateScopedProcessTarget
          targetKey previousOwner previousSite ownerKey siteKey

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
