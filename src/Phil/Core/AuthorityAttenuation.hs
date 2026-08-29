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

import qualified AuthorityAttenuationKernel as AuthorityAttenuationKernel
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
  = AuthorityAttenuationKernelBridgeMismatch
  | AuthorityAttenuationSubjectMismatch AuthoritySubjectKey AuthoritySubjectKey
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

-- | Check one explicit attenuation relation. Concrete equality and Set facts
-- remain native representation facts; the extracted PHIL-AUTH-ATTEN-001 kernel
-- owns final semantic acceptance. Handwritten diagnostics can only explain a
-- kernel rejection, never turn one into success.
checkExplicitAuthorityAttenuation
  :: AuthoritySurface
  -> AuthoritySurface
  -> AuthorityAttenuationWitness
  -> Either AuthorityAttenuationError CheckedAuthorityAttenuation
checkExplicitAuthorityAttenuation source target witness =
  case decision of
    True
      | allFacts -> Right CheckedAuthorityAttenuation
          { checkedAuthorityAttenuationSource = source
          , checkedAuthorityAttenuationTarget = target
          , checkedAuthorityAttenuationWitness = witness
          }
      | otherwise -> Left AuthorityAttenuationKernelBridgeMismatch
    False
      | not subjectMatches -> Left (AuthorityAttenuationSubjectMismatch
          (authoritySurfaceSubject source)
          (authoritySurfaceSubject target))
      | not noWiden -> Left (AuthorityAttenuationWouldWiden excess)
      | not witnessSourceMatches -> Left (AuthorityAttenuationWitnessSourceMismatch
          (authoritySurfaceContract source)
          (authorityAttenuationSourceContract witness))
      | not witnessTargetMatches -> Left (AuthorityAttenuationWitnessTargetMismatch
          (authoritySurfaceContract target)
          (authorityAttenuationTargetContract witness))
      | not witnessSubjectMatches -> Left (AuthorityAttenuationWitnessSubjectMismatch
          (authoritySurfaceSubject target)
          (authorityAttenuationSubject witness))
      | not witnessOperationsMatch -> Left (AuthorityAttenuationWitnessOperationsMismatch
          (authoritySurfaceOperations target)
          (authorityAttenuationVisibleOperations witness))
      | otherwise -> Left AuthorityAttenuationKernelBridgeMismatch
  where
    subjectMatches =
      authoritySurfaceSubject source == authoritySurfaceSubject target
    excess = Set.difference
      (authoritySurfaceOperations target)
      (authoritySurfaceOperations source)
    noWiden = Set.null excess
    witnessSourceMatches =
      authorityAttenuationSourceContract witness == authoritySurfaceContract source
    witnessTargetMatches =
      authorityAttenuationTargetContract witness == authoritySurfaceContract target
    witnessSubjectMatches =
      authorityAttenuationSubject witness == authoritySurfaceSubject target
    witnessOperationsMatch =
      authorityAttenuationVisibleOperations witness == authoritySurfaceOperations target
    allFacts = and
      [ subjectMatches
      , noWiden
      , witnessSourceMatches
      , witnessTargetMatches
      , witnessSubjectMatches
      , witnessOperationsMatch
      ]
    decision = AuthorityAttenuationKernel.decideExplicitAuthorityAttenuation
      subjectMatches
      noWiden
      witnessSourceMatches
      witnessTargetMatches
      witnessSubjectMatches
      witnessOperationsMatch

-- | Check authority visibility at a semantic boundary. Keeping the same
-- authority contract requires the same visible authority surface. Presenting a
-- different, narrower contract requires an explicit checked attenuation. The
-- extracted kernel owns the final same-contract/changed-contract acceptance
-- choice; concrete witness reconstruction remains native and fail closed.
checkAuthorityBoundary
  :: AuthorityBoundaryKind
  -> AuthoritySurface
  -> AuthoritySurface
  -> Maybe AuthorityAttenuationWitness
  -> Either AuthorityAttenuationError CheckedAuthorityBoundary
checkAuthorityBoundary kind available visible maybeWitness =
  case decision of
    True
      | not subjectMatches || not noWiden ->
          Left AuthorityAttenuationKernelBridgeMismatch
      | sameContract && sameSurface -> Right CheckedAuthorityBoundary
          { checkedAuthorityBoundaryKind = kind
          , checkedAuthorityBoundaryAvailable = available
          , checkedAuthorityBoundaryVisible = visible
          , checkedAuthorityBoundaryAttenuation = Nothing
          }
      | changedContract -> case maybeWitness of
          Just witness -> do
            checked <- checkExplicitAuthorityAttenuation available visible witness
            Right CheckedAuthorityBoundary
              { checkedAuthorityBoundaryKind = kind
              , checkedAuthorityBoundaryAvailable = available
              , checkedAuthorityBoundaryVisible = visible
              , checkedAuthorityBoundaryAttenuation = Just checked
              }
          Nothing -> Left AuthorityAttenuationKernelBridgeMismatch
      | otherwise -> Left AuthorityAttenuationKernelBridgeMismatch
    False
      | not subjectMatches -> Left (AuthorityAttenuationSubjectMismatch
          (authoritySurfaceSubject available)
          (authoritySurfaceSubject visible))
      | not noWiden -> Left (AuthorityAttenuationWouldWiden excess)
      | sameContract && not sameSurface ->
          Left (AuthorityBoundarySameContractSurfaceMismatch
            kind
            (authoritySurfaceOperations available)
            (authoritySurfaceOperations visible))
      | changedContract -> case maybeWitness of
          Nothing -> Left (AuthorityBoundaryContractChangeWithoutAttenuation
            kind
            (authoritySurfaceContract available)
            (authoritySurfaceContract visible))
          Just witness -> case checkExplicitAuthorityAttenuation available visible witness of
            Left err -> Left err
            Right _ -> Left AuthorityAttenuationKernelBridgeMismatch
      | otherwise -> Left AuthorityAttenuationKernelBridgeMismatch
  where
    subjectMatches =
      authoritySurfaceSubject available == authoritySurfaceSubject visible
    excess = Set.difference
      (authoritySurfaceOperations visible)
      (authoritySurfaceOperations available)
    noWiden = Set.null excess
    sameContract =
      authoritySurfaceContract available == authoritySurfaceContract visible
    sameSurface =
      authoritySurfaceOperations available == authoritySurfaceOperations visible
    changedContract = not sameContract
    attenuationWitnessValid = case maybeWitness of
      Nothing -> False
      Just witness -> explicitAuthorityFactsAccepted available visible witness
    decision = AuthorityAttenuationKernel.decideAuthorityBoundary
      subjectMatches
      noWiden
      sameContract
      sameSurface
      changedContract
      attenuationWitnessValid

-- | Join one authority-bearing value across continuing branches. Native finite
-- list traversal and Set intersection supply exact branch facts; the extracted
-- kernel owns final acceptance and the explicit nonempty-branch requirement.
checkAuthorityJoin
  :: [AuthoritySurface]
  -> AuthoritySurface
  -> Either AuthorityAttenuationError AuthoritySurface
checkAuthorityJoin surfaces joined =
  case decision of
    True
      | hasContinuingBranch && subjectsMatch && contractsMatch && operationsDoNotWiden ->
          Right joined
      | otherwise -> Left AuthorityAttenuationKernelBridgeMismatch
    False
      | not hasContinuingBranch -> Left AuthorityJoinEmpty
      | not subjectsMatch -> case subjectMismatches of
          actual : _ -> Left (AuthorityJoinSubjectMismatch
            (authoritySurfaceSubject joined)
            actual)
          [] -> Left AuthorityAttenuationKernelBridgeMismatch
      | not contractsMatch -> case contractMismatches of
          actual : _ -> Left (AuthorityJoinContractChangeWithoutAttenuation
            actual
            (authoritySurfaceContract joined))
          [] -> Left AuthorityAttenuationKernelBridgeMismatch
      | not operationsDoNotWiden -> Left (AuthorityJoinWouldWiden excess)
      | otherwise -> Left AuthorityAttenuationKernelBridgeMismatch
  where
    hasContinuingBranch = not (null surfaces)
    subjectMismatches =
      [ authoritySurfaceSubject surface
      | surface <- surfaces
      , authoritySurfaceSubject surface /= authoritySurfaceSubject joined
      ]
    subjectsMatch = null subjectMismatches
    contractMismatches =
      [ authoritySurfaceContract surface
      | surface <- surfaces
      , authoritySurfaceContract surface /= authoritySurfaceContract joined
      ]
    contractsMatch = null contractMismatches
    commonOperations = case surfaces of
      [] -> Set.empty
      firstSurface : rest -> foldr
        (Set.intersection . authoritySurfaceOperations)
        (authoritySurfaceOperations firstSurface)
        rest
    excess = Set.difference (authoritySurfaceOperations joined) commonOperations
    operationsDoNotWiden = Set.null excess
    decision = AuthorityAttenuationKernel.decideAuthorityJoin
      hasContinuingBranch
      subjectsMatch
      contractsMatch
      operationsDoNotWiden

explicitAuthorityFactsAccepted
  :: AuthoritySurface
  -> AuthoritySurface
  -> AuthorityAttenuationWitness
  -> Bool
explicitAuthorityFactsAccepted source target witness = and
  [ authoritySurfaceSubject source == authoritySurfaceSubject target
  , Set.null (Set.difference
      (authoritySurfaceOperations target)
      (authoritySurfaceOperations source))
  , authorityAttenuationSourceContract witness == authoritySurfaceContract source
  , authorityAttenuationTargetContract witness == authoritySurfaceContract target
  , authorityAttenuationSubject witness == authoritySurfaceSubject target
  , authorityAttenuationVisibleOperations witness == authoritySurfaceOperations target
  ]
