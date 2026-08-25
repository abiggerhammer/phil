{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.AuthorityAttenuation
  ( AuthoritySurface (..)
  , AuthorityAttenuationWitness (..)
  , AuthorityBoundaryKind (..)
  , CheckedAuthorityAttenuation (..)
  , CheckedAuthorityBoundary (..)
  , AuthorityAttenuationError (..)
  , authoritySurfaceFromCapability
  , checkExplicitAuthorityAttenuation
  , checkAuthorityBoundary
  , checkAuthorityJoin
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Authority
  ( AuthorityCapability (..)
  , AuthorityContractKey
  , AuthorityOperationKey
  , AuthoritySubjectKey
  )

-- | Public semantic authority visible through one capability boundary.
-- Runtime representation, provider symbols, and capability occurrence identity
-- are intentionally absent: this relation is about authority visibility, not
-- ownership of a particular term occurrence.
data AuthoritySurface = AuthoritySurface
  { authoritySurfaceContract :: AuthorityContractKey
  , authoritySurfaceSubject :: AuthoritySubjectKey
  , authoritySurfaceOperations :: Set.Set AuthorityOperationKey
  }
  deriving (Eq, Ord, Show)

-- | Explicit checked relation permitting a broader authority contract to be
-- presented through a narrower one for the same semantic subject. The witness
-- is exact: it names both contracts, the subject, and the complete operation set
-- exposed by the attenuated contract.
data AuthorityAttenuationWitness = AuthorityAttenuationWitness
  { authorityAttenuationSourceContract :: AuthorityContractKey
  , authorityAttenuationTargetContract :: AuthorityContractKey
  , authorityAttenuationSubject :: AuthoritySubjectKey
  , authorityAttenuationVisibleOperations :: Set.Set AuthorityOperationKey
  }
  deriving (Eq, Ord, Show)

-- | Boundaries named by ADR-014 where authority may be narrowed but never
-- silently widened. The same semantic rule is deliberately reused instead of
-- inventing separate authority lattices for generics, callables, and providers.
data AuthorityBoundaryKind
  = AuthorityGenericBinding
  | AuthorityCallableSubstitution
  | AuthorityProviderReplacement
  | AuthorityArchitectureBoundary
  | AuthorityOtherBoundary Text
  deriving (Eq, Ord, Show)

data CheckedAuthorityAttenuation = CheckedAuthorityAttenuation
  { checkedAuthorityAttenuationSource :: AuthoritySurface
  , checkedAuthorityAttenuationTarget :: AuthoritySurface
  , checkedAuthorityAttenuationWitness :: AuthorityAttenuationWitness
  }
  deriving (Eq, Ord, Show)

data CheckedAuthorityBoundary = CheckedAuthorityBoundary
  { checkedAuthorityBoundaryKind :: AuthorityBoundaryKind
  , checkedAuthorityBoundaryAvailable :: AuthoritySurface
  , checkedAuthorityBoundaryVisible :: AuthoritySurface
  , checkedAuthorityBoundaryAttenuation :: Maybe CheckedAuthorityAttenuation
  }
  deriving (Eq, Ord, Show)

data AuthorityAttenuationError
  = AuthorityAttenuationSubjectMismatch AuthoritySubjectKey AuthoritySubjectKey
  | AuthorityAttenuationWouldWiden (Set.Set AuthorityOperationKey)
  | AuthorityAttenuationWitnessSourceMismatch AuthorityContractKey AuthorityContractKey
  | AuthorityAttenuationWitnessTargetMismatch AuthorityContractKey AuthorityContractKey
  | AuthorityAttenuationWitnessSubjectMismatch AuthoritySubjectKey AuthoritySubjectKey
  | AuthorityAttenuationWitnessOperationsMismatch
      (Set.Set AuthorityOperationKey)
      (Set.Set AuthorityOperationKey)
  | AuthorityBoundaryContractChangeWithoutAttenuation
      AuthorityBoundaryKind
      AuthorityContractKey
      AuthorityContractKey
  | AuthorityBoundarySameContractSurfaceMismatch
      AuthorityBoundaryKind
      (Set.Set AuthorityOperationKey)
      (Set.Set AuthorityOperationKey)
  | AuthorityJoinEmpty
  | AuthorityJoinSubjectMismatch AuthoritySubjectKey AuthoritySubjectKey
  | AuthorityJoinWouldWiden (Set.Set AuthorityOperationKey)
  | AuthorityJoinContractChangeWithoutAttenuation
      AuthorityContractKey
      AuthorityContractKey
  deriving (Eq, Ord, Show)

authoritySurfaceFromCapability :: AuthorityCapability -> AuthoritySurface
authoritySurfaceFromCapability capability = AuthoritySurface
  { authoritySurfaceContract = authorityCapabilityContract capability
  , authoritySurfaceSubject = authorityCapabilitySubject capability
  , authoritySurfaceOperations = authorityCapabilityOperations capability
  }

-- | Check one explicit attenuation relation. Authority may only shrink, and the
-- subject may not change. Changing the public authority contract requires this
-- exact witness so a contract rename or nominal coincidence cannot masquerade
-- as semantic refinement.
checkExplicitAuthorityAttenuation
  :: AuthoritySurface
  -> AuthoritySurface
  -> AuthorityAttenuationWitness
  -> Either AuthorityAttenuationError CheckedAuthorityAttenuation
checkExplicitAuthorityAttenuation source target witness
  | authoritySurfaceSubject source /= authoritySurfaceSubject target =
      Left (AuthorityAttenuationSubjectMismatch
        (authoritySurfaceSubject source)
        (authoritySurfaceSubject target))
  | not (Set.null excess) = Left (AuthorityAttenuationWouldWiden excess)
  | authorityAttenuationSourceContract witness /= authoritySurfaceContract source =
      Left (AuthorityAttenuationWitnessSourceMismatch
        (authoritySurfaceContract source)
        (authorityAttenuationSourceContract witness))
  | authorityAttenuationTargetContract witness /= authoritySurfaceContract target =
      Left (AuthorityAttenuationWitnessTargetMismatch
        (authoritySurfaceContract target)
        (authorityAttenuationTargetContract witness))
  | authorityAttenuationSubject witness /= authoritySurfaceSubject target =
      Left (AuthorityAttenuationWitnessSubjectMismatch
        (authoritySurfaceSubject target)
        (authorityAttenuationSubject witness))
  | authorityAttenuationVisibleOperations witness /= authoritySurfaceOperations target =
      Left (AuthorityAttenuationWitnessOperationsMismatch
        (authoritySurfaceOperations target)
        (authorityAttenuationVisibleOperations witness))
  | otherwise = Right CheckedAuthorityAttenuation
      { checkedAuthorityAttenuationSource = source
      , checkedAuthorityAttenuationTarget = target
      , checkedAuthorityAttenuationWitness = witness
      }
  where
    excess = Set.difference
      (authoritySurfaceOperations target)
      (authoritySurfaceOperations source)

-- | Check authority visibility at a semantic boundary. Keeping the same
-- authority contract requires the same visible authority surface. Presenting a
-- different, narrower contract requires an explicit checked attenuation. No
-- boundary may infer extra operations merely because the concrete input has a
-- richer implementation, representation, or provider behind it.
checkAuthorityBoundary
  :: AuthorityBoundaryKind
  -> AuthoritySurface
  -> AuthoritySurface
  -> Maybe AuthorityAttenuationWitness
  -> Either AuthorityAttenuationError CheckedAuthorityBoundary
checkAuthorityBoundary kind available visible maybeWitness
  | authoritySurfaceSubject available /= authoritySurfaceSubject visible =
      Left (AuthorityAttenuationSubjectMismatch
        (authoritySurfaceSubject available)
        (authoritySurfaceSubject visible))
  | not (Set.null excess) = Left (AuthorityAttenuationWouldWiden excess)
  | authoritySurfaceContract available == authoritySurfaceContract visible =
      if authoritySurfaceOperations available == authoritySurfaceOperations visible
        then Right CheckedAuthorityBoundary
          { checkedAuthorityBoundaryKind = kind
          , checkedAuthorityBoundaryAvailable = available
          , checkedAuthorityBoundaryVisible = visible
          , checkedAuthorityBoundaryAttenuation = Nothing
          }
        else Left (AuthorityBoundarySameContractSurfaceMismatch
          kind
          (authoritySurfaceOperations available)
          (authoritySurfaceOperations visible))
  | otherwise = case maybeWitness of
      Nothing -> Left (AuthorityBoundaryContractChangeWithoutAttenuation
        kind
        (authoritySurfaceContract available)
        (authoritySurfaceContract visible))
      Just witness -> do
        checked <- checkExplicitAuthorityAttenuation available visible witness
        Right CheckedAuthorityBoundary
          { checkedAuthorityBoundaryKind = kind
          , checkedAuthorityBoundaryAvailable = available
          , checkedAuthorityBoundaryVisible = visible
          , checkedAuthorityBoundaryAttenuation = Just checked
          }
  where
    excess = Set.difference
      (authoritySurfaceOperations visible)
      (authoritySurfaceOperations available)

-- | Join one authority-bearing value across continuing branches. The joined
-- visible surface must be available on every branch; the checker never unions
-- branch-local authority. Contract changes at a join are deliberately rejected
-- in this first slice and must instead be made explicit before the join.
checkAuthorityJoin
  :: [AuthoritySurface]
  -> AuthoritySurface
  -> Either AuthorityAttenuationError AuthoritySurface
checkAuthorityJoin [] _ = Left AuthorityJoinEmpty
checkAuthorityJoin (firstSurface : rest) joined = do
  mapM_ checkSubject (firstSurface : rest)
  mapM_ checkContract (firstSurface : rest)
  let commonOperations = foldr
        (Set.intersection . authoritySurfaceOperations)
        (authoritySurfaceOperations firstSurface)
        rest
      excess = Set.difference (authoritySurfaceOperations joined) commonOperations
  if Set.null excess
    then Right joined
    else Left (AuthorityJoinWouldWiden excess)
  where
    checkSubject surface
      | authoritySurfaceSubject surface == authoritySurfaceSubject joined = Right ()
      | otherwise = Left (AuthorityJoinSubjectMismatch
          (authoritySurfaceSubject joined)
          (authoritySurfaceSubject surface))
    checkContract surface
      | authoritySurfaceContract surface == authoritySurfaceContract joined = Right ()
      | otherwise = Left (AuthorityJoinContractChangeWithoutAttenuation
          (authoritySurfaceContract surface)
          (authoritySurfaceContract joined))
