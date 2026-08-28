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

import qualified AuthorityPossessionKernel as AuthorityPossessionKernel
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
  | AuthorityPossessionKernelBridgeMismatch
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

-- | Establish permission to exercise one semantic authority operation. Concrete
-- occurrence lookup and finite Set membership remain native representation
-- facts; the extracted PHIL-AUTH-POSSESS-001 kernel owns final semantic
-- rejection precedence and acceptance. Native facts are checked against the
-- returned decision so a representation/kernel disagreement can only fail
-- closed.
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
    let contractMatches =
          authorityCapabilityContract capability == requiredAuthorityContract requirement
        subjectMatches =
          authorityCapabilitySubject capability == requiredAuthoritySubject requirement
        operationPermitted = Set.member
          (requiredAuthorityOperation requirement)
          (authorityCapabilityOperations capability)
        decision = AuthorityPossessionKernel.decideAuthorityExerciseFacts
          AuthorityPossessionKernel.True
          (toAuthorityPossessionKernelBool contractMatches)
          (toAuthorityPossessionKernelBool subjectMatches)
          (toAuthorityPossessionKernelBool operationPermitted)
    case decision of
      AuthorityPossessionKernel.AuthorityExerciseAccepted
        | contractMatches && subjectMatches && operationPermitted ->
            Right CheckedAuthorityExercise
              { checkedAuthorityRequirement = requirement
              , checkedAuthorityCapability = capability
              }
        | otherwise -> Left AuthorityPossessionKernelBridgeMismatch
      AuthorityPossessionKernel.AuthorityExerciseContractRejected
        | not contractMatches -> Left (AuthorityContractMismatch
            (requiredAuthorityContract requirement)
            (authorityCapabilityContract capability))
        | otherwise -> Left AuthorityPossessionKernelBridgeMismatch
      AuthorityPossessionKernel.AuthorityExerciseSubjectRejected
        | contractMatches && not subjectMatches -> Left (AuthoritySubjectMismatch
            (requiredAuthoritySubject requirement)
            (authorityCapabilitySubject capability))
        | otherwise -> Left AuthorityPossessionKernelBridgeMismatch
      AuthorityPossessionKernel.AuthorityExerciseOperationRejected
        | contractMatches && subjectMatches && not operationPermitted ->
            Left (AuthorityOperationNotPermitted
              (requiredAuthorityOperation requirement))
        | otherwise -> Left AuthorityPossessionKernelBridgeMismatch
      AuthorityPossessionKernel.AuthorityExerciseSourceRejected ->
        Left AuthorityPossessionKernelBridgeMismatch
  _ ->
    case AuthorityPossessionKernel.decideAuthorityExerciseFacts
        AuthorityPossessionKernel.False
        AuthorityPossessionKernel.False
        AuthorityPossessionKernel.False
        AuthorityPossessionKernel.False of
      AuthorityPossessionKernel.AuthorityExerciseSourceRejected ->
        Left (AuthoritySourceIsNotPossession source)
      _ -> Left AuthorityPossessionKernelBridgeMismatch

-- | Ordinary contraction for an authority-bearing value. Concrete lookup and
-- target freshness remain native; the extracted kernel decides structural copy
-- legality from the exact bridged Mode. A kernel/native disagreement rejects.
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
    else
      let mode = authorityCapabilityMode source
      in case AuthorityPossessionKernel.decideAuthorityCopy
          (toAuthorityPossessionKernelMode mode) of
        AuthorityPossessionKernel.AuthorityCopyAccepted
          | mode == Unrestricted -> Right (AuthorityState
              (Map.insert targetKey
                (source { authorityCapabilityOccurrence = targetKey })
                capabilities))
          | otherwise -> Left AuthorityPossessionKernelBridgeMismatch
        AuthorityPossessionKernel.AuthorityCopyRejected
          | mode /= Unrestricted -> Left (RestrictedCapabilityCopy sourceKey mode)
          | otherwise -> Left AuthorityPossessionKernelBridgeMismatch
  where
    capabilities = authorityStateCapabilities state

-- | Ordinary weakening for an authority-bearing value. Concrete lookup and
-- state deletion remain native; the extracted kernel decides structural drop
-- legality from the exact bridged Mode. A kernel/native disagreement rejects.
dropAuthorityCapability
  :: CapabilityOccurrenceKey
  -> AuthorityState
  -> Either AuthorityCheckError AuthorityState
dropAuthorityCapability key state = do
  capability <- maybe
    (Left (UnknownCapabilityOccurrence key))
    Right
    (lookupAuthorityCapability key state)
  let mode = authorityCapabilityMode capability
  case AuthorityPossessionKernel.decideAuthorityDrop
      (toAuthorityPossessionKernelMode mode) of
    AuthorityPossessionKernel.AuthorityDropAccepted
      | mode /= Linear -> Right (AuthorityState (Map.delete key capabilities))
      | otherwise -> Left AuthorityPossessionKernelBridgeMismatch
    AuthorityPossessionKernel.AuthorityDropRejected
      | mode == Linear -> Left (LinearCapabilityDrop key)
      | otherwise -> Left AuthorityPossessionKernelBridgeMismatch
  where
    capabilities = authorityStateCapabilities state

toAuthorityPossessionKernelBool :: Bool -> AuthorityPossessionKernel.Bool
toAuthorityPossessionKernelBool value = case value of
  True -> AuthorityPossessionKernel.True
  False -> AuthorityPossessionKernel.False

toAuthorityPossessionKernelMode :: Mode -> AuthorityPossessionKernel.Mode
toAuthorityPossessionKernelMode mode = case mode of
  Unrestricted -> AuthorityPossessionKernel.Unrestricted
  Affine -> AuthorityPossessionKernel.Affine
  Linear -> AuthorityPossessionKernel.Linear
