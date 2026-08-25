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
  = ClosurePublicAuthorityNotReachable (Set.Set AuthorityUse)
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

-- | Check the pure-Phil closure confinement relation. Broader internal authority
-- is legal when the checked body remains inside the public mediated authority.
-- A public authority promise must itself be realizable from the closure's exact
-- reachable environment in this bounded per-instance model.
checkClosureAuthorityConfinement
  :: ClosureAuthorityConfinementSpec
  -> Either AuthorityConfinementError CheckedClosureAuthorityConfinement
checkClosureAuthorityConfinement spec
  | not (Set.null publicNotReachable) =
      Left (ClosurePublicAuthorityNotReachable publicNotReachable)
  | not (Set.null exercisedNotReachable) =
      Left (ClosureExercisedAuthorityNotReachable exercisedNotReachable)
  | not (Set.null exercisedOutsidePublic) =
      Left (ClosureExercisedAuthorityExceedsPublic exercisedOutsidePublic)
  | otherwise = Right CheckedClosureAuthorityConfinement
      { checkedClosureReachableAuthority = reachable
      , checkedClosurePublicMediatedAuthority = public
      , checkedClosureExercisedAuthority = exercised
      , checkedClosureAuthorityOrigins = closureReachableAuthority spec
      }
  where
    reachable = reachableAuthorityUses (closureReachableAuthority spec)
    public = closurePublicMediatedAuthority spec
    exercised = closureExercisedAuthority spec
    publicNotReachable = Set.difference public reachable
    exercisedNotReachable = Set.difference exercised reachable
    exercisedOutsidePublic = Set.difference exercised public

-- | Prove one negative reachable-authority claim from an already checked closure
-- summary. Narrow public behavior is not enough: the claim fails whenever any
-- captured capability or callable still makes the operation reachable for the
-- exact subject, even if checked body confinement proves that operation is not
-- exercised through the current public callable interface.
checkNegativeAuthorityClaim
  :: CheckedClosureAuthorityConfinement
  -> NegativeAuthorityClaim
  -> Either AuthorityConfinementError CheckedNegativeAuthorityClaim
checkNegativeAuthorityClaim checked claim
  | Set.null origins = Right CheckedNegativeAuthorityClaim
      { checkedNegativeAuthorityClaim = claim
      , checkedNegativeAuthorityReachableSet = checkedClosureReachableAuthority checked
      }
  | otherwise = Left (NegativeAuthorityClaimFalse claim origins)
  where
    targetUse = AuthorityUse
      (negativeAuthoritySubject claim)
      (negativeAuthorityOperation claim)
    origins = Set.fromList
      [ reachableAuthorityOrigin grant
      | grant <- checkedClosureAuthorityOrigins checked
      , Set.member targetUse (authorityUsesForSurface (reachableAuthoritySurface grant))
      ]
