{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessParticipants
  ( ProtocolRoleOccurrence (..)
  , ParticipantSourceTarget (..)
  , ParticipantDeclaration (..)
  , CheckedParticipant (..)
  , ParticipantClassification (..)
  , ParticipantClassificationError (..)
  , checkParticipantClassifications
  ) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Process
  ( ActivationStatus (..)
  , ProcessKey
  , ProcessNetwork (..)
  , ProcessOccurrence (..)
  )
import Phil.Core.Protocol
  ( ProtocolInstanceRevision
  , ProtocolRoleKey
  )
import Phil.Core.Static
  ( ArchitectureInstanceGraph (..)
  , ArchitectureInstanceIdentity (..)
  , CheckedArchitectureInstance (..)
  , InstanceKey
  )

-- | One exact role occurrence of one exact protocol instance. Equal-looking
-- role/session syntax in another protocol instance is a different occurrence.
data ProtocolRoleOccurrence = ProtocolRoleOccurrence
  { roleOccurrenceInstance :: ProtocolInstanceRevision
  , roleOccurrenceRole :: ProtocolRoleKey
  }
  deriving (Eq, Ord, Show)

-- | The two source-author choices admitted by Grammar v1:
--
--     role P.r = worker;
--     role P.r = external;
--
-- InternalParticipantTarget names an already-existing executable architecture
-- occurrence. It does not instantiate a process target.
data ParticipantSourceTarget
  = InternalParticipantTarget InstanceKey
  | ExternalParticipantTarget
  deriving (Eq, Ord, Show)

data ParticipantDeclaration = ParticipantDeclaration
  { participantDeclaredRole :: ProtocolRoleOccurrence
  , participantDeclaredTarget :: ParticipantSourceTarget
  }
  deriving (Eq, Ord, Show)

-- | Deliberately narrow checked result. External classification carries no
-- transport, BoundaryRepresentation, entry, authority, assumption, export, or
-- realization payload; those remain separate competent relations.
data CheckedParticipant
  = CheckedInternalParticipant
      { checkedParticipantRole :: ProtocolRoleOccurrence
      , checkedParticipantTarget :: InstanceKey
      , checkedParticipantProcess :: ProcessKey
      }
  | CheckedExternalParticipant
      { checkedParticipantRole :: ProtocolRoleOccurrence
      }
  deriving (Eq, Ord, Show)

newtype ParticipantClassification = ParticipantClassification
  { participantClassifications :: Map.Map ProtocolRoleOccurrence CheckedParticipant
  }
  deriving (Eq, Show)

data ParticipantClassificationError
  = ParticipantArchitectureRootMismatch
  | DuplicateExpectedRole ProtocolRoleOccurrence
  | DuplicateParticipantDeclaration ProtocolRoleOccurrence
  | UnexpectedParticipantDeclaration ProtocolRoleOccurrence
  | MissingParticipantClassification ProtocolRoleOccurrence
  | UnknownInternalParticipantTarget ProtocolRoleOccurrence InstanceKey
  | InternalParticipantTargetUnactivated ProtocolRoleOccurrence InstanceKey
  | InternalParticipantTargetAmbiguous ProtocolRoleOccurrence InstanceKey [ProcessKey]
  | InternalParticipantProcessNotActive ProtocolRoleOccurrence ProcessKey ActivationStatus
  deriving (Eq, Show)

checkParticipantClassifications
  :: ArchitectureInstanceGraph
  -> ProcessNetwork
  -> [ProtocolRoleOccurrence]
  -> [ParticipantDeclaration]
  -> Either ParticipantClassificationError ParticipantClassification
checkParticipantClassifications graph network expectedRoles declarations = do
  if architectureGraphRoot graph == processNetworkRoot network
    then Right ()
    else Left ParticipantArchitectureRootMismatch
  expected <- normalizeExpectedRoles expectedRoles
  declared <- normalizeDeclarations declarations
  case Set.lookupMin (Map.keysSet declared `Set.difference` expected) of
    Just role -> Left (UnexpectedParticipantDeclaration role)
    Nothing -> Right ()
  case Set.lookupMin (expected `Set.difference` Map.keysSet declared) of
    Just role -> Left (MissingParticipantClassification role)
    Nothing -> Right ()
  checked <- Map.traverseWithKey checkOne declared
  pure (ParticipantClassification checked)
  where
    checkOne role target =
      case target of
        ExternalParticipantTarget ->
          Right (CheckedExternalParticipant role)
        InternalParticipantTarget targetKey -> do
          requireArchitectureTarget role targetKey
          processKey <- resolveInternalProcess role targetKey
          occurrence <- case Map.lookup processKey (processNetworkPopulation network) of
            Nothing -> Left (InternalParticipantTargetUnactivated role targetKey)
            Just value -> Right value
          case processOccurrenceActivation occurrence of
            Active -> Right (CheckedInternalParticipant role targetKey processKey)
            status -> Left (InternalParticipantProcessNotActive role processKey status)

    requireArchitectureTarget role targetKey =
      case Map.lookup targetKey (architectureGraphInstances graph) of
        Nothing -> Left (UnknownInternalParticipantTarget role targetKey)
        Just checked
          | identityInstanceKey (checkedArchitectureIdentity checked) == targetKey -> Right ()
          | otherwise -> Left (UnknownInternalParticipantTarget role targetKey)

    resolveInternalProcess role targetKey =
      case
        [ processKey
        | (processKey, occurrence) <- Map.toAscList (processNetworkPopulation network)
        , identityInstanceKey (processOccurrenceTarget occurrence) == targetKey
        ] of
          [] -> Left (InternalParticipantTargetUnactivated role targetKey)
          [processKey] -> Right processKey
          processKeys -> Left (InternalParticipantTargetAmbiguous role targetKey processKeys)

normalizeExpectedRoles
  :: [ProtocolRoleOccurrence]
  -> Either ParticipantClassificationError (Set.Set ProtocolRoleOccurrence)
normalizeExpectedRoles = foldl' insertOne (Right Set.empty)
  where
    insertOne accumulated role = do
      current <- accumulated
      if Set.member role current
        then Left (DuplicateExpectedRole role)
        else Right (Set.insert role current)

normalizeDeclarations
  :: [ParticipantDeclaration]
  -> Either ParticipantClassificationError (Map.Map ProtocolRoleOccurrence ParticipantSourceTarget)
normalizeDeclarations = foldl' insertOne (Right Map.empty)
  where
    insertOne accumulated declaration = do
      current <- accumulated
      let role = participantDeclaredRole declaration
      if Map.member role current
        then Left (DuplicateParticipantDeclaration role)
        else Right (Map.insert role (participantDeclaredTarget declaration) current)
