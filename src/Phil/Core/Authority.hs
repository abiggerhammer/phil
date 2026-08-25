{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Authority
  ( CapabilityOccurrenceKey (..)
  , AuthorityContractKey (..)
  , AuthoritySubjectKey (..)
  , AuthorityOperationKey (..)
  , AuthorityRequirement (..)
  , AuthorityCapability (..)
  , AuthorityState (..)
  , AuthorityExerciseSource (..)
  , CheckedAuthorityExercise (..)
  , AuthorityCheckError (..)
  , emptyAuthorityState
  , insertAuthorityCapability
  , lookupAuthorityCapability
  , checkAuthorityExercise
  , copyAuthorityCapability
  , dropAuthorityCapability
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Syntax (Mode (..))

newtype CapabilityOccurrenceKey = CapabilityOccurrenceKey
  { unCapabilityOccurrenceKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype AuthorityContractKey = AuthorityContractKey
  { unAuthorityContractKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype AuthoritySubjectKey = AuthoritySubjectKey
  { unAuthoritySubjectKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype AuthorityOperationKey = AuthorityOperationKey
  { unAuthorityOperationKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact semantic authority demanded by one operation. Runtime handles,
-- imported declarations, symbols, and effect permissions are deliberately
-- absent: they may help locate or realize an operation but cannot satisfy this
-- possession requirement by themselves.
data AuthorityRequirement = AuthorityRequirement
  { requiredAuthorityContract :: AuthorityContractKey
  , requiredAuthoritySubject :: AuthoritySubjectKey
  , requiredAuthorityOperation :: AuthorityOperationKey
  }
  deriving (Eq, Ord, Show)

-- | One actually possessed authority-bearing value. Structural mode governs
-- possession of this value; it is independent of how any particular operation
-- borrows, preserves, transforms, or consumes it.
data AuthorityCapability = AuthorityCapability
  { authorityCapabilityOccurrence :: CapabilityOccurrenceKey
  , authorityCapabilityContract :: AuthorityContractKey
  , authorityCapabilitySubject :: AuthoritySubjectKey
  , authorityCapabilityMode :: Mode
  , authorityCapabilityOperations :: Set.Set AuthorityOperationKey
  }
  deriving (Eq, Ord, Show)

newtype AuthorityState = AuthorityState
  { authorityStateCapabilities
      :: Map.Map CapabilityOccurrenceKey AuthorityCapability
  }
  deriving (Eq, Ord, Show)

-- | Sources that code might try to mistake for semantic authority. Only an
-- exact possessed capability occurrence is admissible in pure Phil.
data AuthorityExerciseSource
  = PossessedCapability CapabilityOccurrenceKey
  | ImportedAuthorityDeclaration AuthorityContractKey
  | EffectPermissionOnly Text
  | RuntimeAuthorityHandle Text
  | BackendAuthoritySymbol Text
  | AmbientAuthorityRegistryEntry Text
  deriving (Eq, Ord, Show)

data CheckedAuthorityExercise = CheckedAuthorityExercise
  { checkedAuthorityRequirement :: AuthorityRequirement
  , checkedAuthorityCapability :: AuthorityCapability
  }
  deriving (Eq, Ord, Show)

data AuthorityCheckError
  = DuplicateCapabilityOccurrence CapabilityOccurrenceKey
  | UnknownCapabilityOccurrence CapabilityOccurrenceKey
  | AuthoritySourceIsNotPossession AuthorityExerciseSource
  | AuthorityContractMismatch AuthorityContractKey AuthorityContractKey
  | AuthoritySubjectMismatch AuthoritySubjectKey AuthoritySubjectKey
  | AuthorityOperationNotPermitted AuthorityOperationKey
  | RestrictedCapabilityCopy CapabilityOccurrenceKey Mode
  | CapabilityCopyTargetAlreadyExists CapabilityOccurrenceKey
  | LinearCapabilityDrop CapabilityOccurrenceKey
  deriving (Eq, Ord, Show)

emptyAuthorityState :: AuthorityState
emptyAuthorityState = AuthorityState Map.empty

insertAuthorityCapability
  :: AuthorityCapability
  -> AuthorityState
  -> Either AuthorityCheckError AuthorityState
insertAuthorityCapability capability state
  | Map.member key capabilities = Left (DuplicateCapabilityOccurrence key)
  | otherwise = Right (AuthorityState (Map.insert key capability capabilities))
  where
    key = authorityCapabilityOccurrence capability
    capabilities = authorityStateCapabilities state

lookupAuthorityCapability
  :: CapabilityOccurrenceKey
  -> AuthorityState
  -> Maybe AuthorityCapability
lookupAuthorityCapability key = Map.lookup key . authorityStateCapabilities

-- | Establish permission to exercise one semantic authority operation. This
-- check establishes possession and exact contract/subject/operation agreement;
-- it does not by itself consume or transform the capability. Operation-specific
-- resource transitions are a separate semantic layer under ADR-014.
checkAuthorityExercise
  :: AuthorityRequirement
  -> AuthorityExerciseSource
  -> AuthorityState
  -> Either AuthorityCheckError CheckedAuthorityExercise
checkAuthorityExercise requirement source state = case source of
  PossessedCapability occurrence -> do
    capability <- maybe
      (Left (UnknownCapabilityOccurrence occurrence))
      Right
      (lookupAuthorityCapability occurrence state)
    if authorityCapabilityContract capability /= requiredAuthorityContract requirement
      then Left (AuthorityContractMismatch
        (requiredAuthorityContract requirement)
        (authorityCapabilityContract capability))
      else if authorityCapabilitySubject capability /= requiredAuthoritySubject requirement
        then Left (AuthoritySubjectMismatch
          (requiredAuthoritySubject requirement)
          (authorityCapabilitySubject capability))
        else if not (Set.member
            (requiredAuthorityOperation requirement)
            (authorityCapabilityOperations capability))
          then Left (AuthorityOperationNotPermitted
            (requiredAuthorityOperation requirement))
          else Right CheckedAuthorityExercise
            { checkedAuthorityRequirement = requirement
            , checkedAuthorityCapability = capability
            }
  _ -> Left (AuthoritySourceIsNotPossession source)

-- | Ordinary contraction for an authority-bearing value. Unrestricted
-- authority may be copied into a fresh occurrence; affine/linear authority may
-- not. Copying does not widen the authority contract, subject, or operation set.
copyAuthorityCapability
  :: CapabilityOccurrenceKey
  -> CapabilityOccurrenceKey
  -> AuthorityState
  -> Either AuthorityCheckError AuthorityState
copyAuthorityCapability sourceKey targetKey state = do
  source <- maybe
    (Left (UnknownCapabilityOccurrence sourceKey))
    Right
    (lookupAuthorityCapability sourceKey state)
  if Map.member targetKey capabilities
    then Left (CapabilityCopyTargetAlreadyExists targetKey)
    else case authorityCapabilityMode source of
      Unrestricted -> Right (AuthorityState
        (Map.insert targetKey
          (source { authorityCapabilityOccurrence = targetKey })
          capabilities))
      mode -> Left (RestrictedCapabilityCopy sourceKey mode)
  where
    capabilities = authorityStateCapabilities state

-- | Ordinary weakening for an authority-bearing value. Unrestricted and affine
-- capabilities may be dropped; linear capabilities retain their lifecycle
-- obligation independently of whether their authority was ever exercised.
dropAuthorityCapability
  :: CapabilityOccurrenceKey
  -> AuthorityState
  -> Either AuthorityCheckError AuthorityState
dropAuthorityCapability key state = do
  capability <- maybe
    (Left (UnknownCapabilityOccurrence key))
    Right
    (lookupAuthorityCapability key state)
  case authorityCapabilityMode capability of
    Linear -> Left (LinearCapabilityDrop key)
    _ -> Right (AuthorityState (Map.delete key capabilities))
  where
    capabilities = authorityStateCapabilities state
