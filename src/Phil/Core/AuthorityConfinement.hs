{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.AuthorityConfinement
  ( AuthorityReachabilityOrigin (..)
  , ReachableAuthorityGrant (..)
  , AuthorityUse (..)
  , ClosureAuthorityConfinementSpec (..)
  , CheckedClosureAuthorityConfinement (..)
  , NegativeAuthorityClaim (..)
  , CheckedNegativeAuthorityClaim (..)
  , AuthorityConfinementError (..)
  , authorityUsesForSurface
  , reachableAuthorityUses
  , checkClosureAuthorityConfinement
  , checkNegativeAuthorityClaim
  ) where

import qualified AuthorityConfinementKernel as AuthorityConfinementKernel
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Authority
  ( AuthorityOperationKey
  , AuthoritySubjectKey
  , CapabilityOccurrenceKey
  )
import Phil.Core.AuthorityAttenuation (AuthoritySurface (..))
import Phil.Core.Callable (CallableOccurrenceKey)

-- | Exact source of authority reachable from one closure environment. This is
-- intentionally source-semantic identity rather than target pointer/layout
-- identity. More origin kinds can be added when provider realization lands.
data AuthorityReachabilityOrigin
  = CapturedCapabilityOrigin CapabilityOccurrenceKey
  | CapturedCallableOrigin CallableOccurrenceKey
  | OtherAuthorityReachabilityOrigin Text
  deriving (Eq, Ord, Show)

-- | One authority surface reachable through a sealed closure environment.
-- Captured capabilities and captured/nested callables both matter for negative
-- authority analysis even when the public callable behavior is narrower.
data ReachableAuthorityGrant = ReachableAuthorityGrant
  { reachableAuthorityOrigin :: AuthorityReachabilityOrigin
  , reachableAuthoritySurface :: AuthoritySurface
  }
  deriving (Eq, Ord, Show)

-- | Subject-specific authority operation. Contract names are deliberately not
-- enough to establish or refute reachability: the negative claim is about the
-- actual semantic operation reachable for the exact subject.
data AuthorityUse = AuthorityUse
  { authorityUseSubject :: AuthoritySubjectKey
  , authorityUseOperation :: AuthorityOperationKey
  }
  deriving (Eq, Ord, Show)

-- | Checked-body inputs for the bounded closure half of AUTH-004.
--
-- * reachable grants describe authority present in the sealed environment;
-- * public mediated authority is the authority the callable interface exposes;
-- * exercised authority comes from checked body analysis.
--
-- A closure may own broader authority than it exposes, but every exercised
-- operation must be both reachable and publicly admitted.
data ClosureAuthorityConfinementSpec = ClosureAuthorityConfinementSpec
  { closureReachableAuthority :: [ReachableAuthorityGrant]
  , closurePublicMediatedAuthority :: Set.Set AuthorityUse
  , closureExercisedAuthority :: Set.Set AuthorityUse
  }
  deriving (Eq, Ord, Show)

data CheckedClosureAuthorityConfinement = CheckedClosureAuthorityConfinement
  { checkedClosureReachableAuthority :: Set.Set AuthorityUse
  , checkedClosurePublicMediatedAuthority :: Set.Set AuthorityUse
  , checkedClosureExercisedAuthority :: Set.Set AuthorityUse
  , checkedClosureAuthorityOrigins :: [ReachableAuthorityGrant]
  }
  deriving (Eq, Ord, Show)

data NegativeAuthorityClaim = NegativeAuthorityClaim
  { negativeAuthoritySubject :: AuthoritySubjectKey
  , negativeAuthorityOperation :: AuthorityOperationKey
  }
  deriving (Eq, Ord, Show)

data CheckedNegativeAuthorityClaim = CheckedNegativeAuthorityClaim
  { checkedNegativeAuthorityClaim :: NegativeAuthorityClaim
  , checkedNegativeAuthorityReachableSet :: Set.Set AuthorityUse
  }
  deriving (Eq, Ord, Show)

data AuthorityConfinementError
  = AuthorityConfinementKernelBridgeMismatch
  | ClosurePublicAuthorityNotReachable (Set.Set AuthorityUse)
  | ClosureExercisedAuthorityNotReachable (Set.Set AuthorityUse)
  | ClosureExercisedAuthorityExceedsPublic (Set.Set AuthorityUse)
  | NegativeAuthorityClaimFalse
      NegativeAuthorityClaim
      (Set.Set AuthorityReachabilityOrigin)
  deriving (Eq, Ord, Show)

-- | Project one exact authority surface into subject-specific reachable uses.
authorityUsesForSurface :: AuthoritySurface -> Set.Set AuthorityUse
authorityUsesForSurface surface = Set.map
  (AuthorityUse (authoritySurfaceSubject surface))
  (authoritySurfaceOperations surface)

-- | Reachability unions internal authority: if any captured value can exercise
-- an operation for a subject, that authority is reachable from the closure.
-- This is intentionally different from control-flow authority joins, which keep
-- only authority common to every continuing branch.
reachableAuthorityUses :: [ReachableAuthorityGrant] -> Set.Set AuthorityUse
reachableAuthorityUses = foldr
  (Set.union . authorityUsesForSurface . reachableAuthoritySurface)
  Set.empty

-- | Check the pure-Phil closure confinement relation. Native Set reflection
-- supplies the three exact subset facts; the extracted PHIL-AUTH-CONFINE-001
-- kernel owns final semantic acceptance. Native diagnostics retain the original
-- rejection precedence and may only fail closed on disagreement.
checkClosureAuthorityConfinement
  :: ClosureAuthorityConfinementSpec
  -> Either AuthorityConfinementError CheckedClosureAuthorityConfinement
checkClosureAuthorityConfinement spec =
  case decision of
    True
      | allFacts -> Right CheckedClosureAuthorityConfinement
          { checkedClosureReachableAuthority = reachable
          , checkedClosurePublicMediatedAuthority = public
          , checkedClosureExercisedAuthority = exercised
          , checkedClosureAuthorityOrigins = closureReachableAuthority spec
          }
      | otherwise -> Left AuthorityConfinementKernelBridgeMismatch
    False
      | not publicSubsetReachable ->
          Left (ClosurePublicAuthorityNotReachable publicNotReachable)
      | not exercisedSubsetReachable ->
          Left (ClosureExercisedAuthorityNotReachable exercisedNotReachable)
      | not exercisedSubsetPublic ->
          Left (ClosureExercisedAuthorityExceedsPublic exercisedOutsidePublic)
      | otherwise -> Left AuthorityConfinementKernelBridgeMismatch
  where
    reachable = reachableAuthorityUses (closureReachableAuthority spec)
    public = closurePublicMediatedAuthority spec
    exercised = closureExercisedAuthority spec
    publicNotReachable = Set.difference public reachable
    exercisedNotReachable = Set.difference exercised reachable
    exercisedOutsidePublic = Set.difference exercised public
    publicSubsetReachable = Set.null publicNotReachable
    exercisedSubsetReachable = Set.null exercisedNotReachable
    exercisedSubsetPublic = Set.null exercisedOutsidePublic
    allFacts = and
      [ publicSubsetReachable
      , exercisedSubsetReachable
      , exercisedSubsetPublic
      ]
    decision = AuthorityConfinementKernel.decideClosureAuthorityConfinement
      publicSubsetReachable
      exercisedSubsetReachable
      exercisedSubsetPublic

-- | Prove one negative reachable-authority claim from an already checked closure
-- summary. The extracted kernel decides absence from the canonical reachable set;
-- retained origin diagnostics must agree with that set or the bridge fails closed.
checkNegativeAuthorityClaim
  :: CheckedClosureAuthorityConfinement
  -> NegativeAuthorityClaim
  -> Either AuthorityConfinementError CheckedNegativeAuthorityClaim
checkNegativeAuthorityClaim checked claim =
  case decision of
    True
      | not authorityReachable && Set.null origins -> Right CheckedNegativeAuthorityClaim
          { checkedNegativeAuthorityClaim = claim
          , checkedNegativeAuthorityReachableSet = reachable
          }
      | otherwise -> Left AuthorityConfinementKernelBridgeMismatch
    False
      | authorityReachable && not (Set.null origins) ->
          Left (NegativeAuthorityClaimFalse claim origins)
      | otherwise -> Left AuthorityConfinementKernelBridgeMismatch
  where
    reachable = checkedClosureReachableAuthority checked
    targetUse = AuthorityUse
      (negativeAuthoritySubject claim)
      (negativeAuthorityOperation claim)
    authorityReachable = Set.member targetUse reachable
    origins = Set.fromList
      [ reachableAuthorityOrigin grant
      | grant <- checkedClosureAuthorityOrigins checked
      , Set.member targetUse (authorityUsesForSurface (reachableAuthoritySurface grant))
      ]
    decision = AuthorityConfinementKernel.decideNegativeAuthorityClaim authorityReachable
