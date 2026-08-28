{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessNetwork
  ( ProcessSiteKey (..)
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
import Phil.Core.Static
  ( ArchitectureInstanceGraph (..)
  , ArchitectureInstanceIdentity (..)
  , CheckedArchitectureInstance (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  )

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
