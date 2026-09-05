{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RuntimePartialityRelation
  ( TargetPartialityKind (..)
  , RuntimePartialityHazardRef (..)
  , RuntimePartialitySourceOutcome (..)
  , RuntimePartialityEnforcementKey (..)
  , RuntimePartialityAssumptionKey (..)
  , RuntimePartialityDeploymentRequirementKey (..)
  , RuntimePartialityDisposition (..)
  , RuntimePartialityRelation (..)
  , CheckedRuntimePartialityRelation
  , RuntimePartialityError (..)
  , checkRuntimePartialityRelation
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (RevisionId (..))
import Phil.Systems.TargetStrengthening
  ( TargetPreconditionRef
  , TargetStrengthening (..)
  , TargetStrengtheningStageBundle (..)
  , TargetStrengtheningVerificationError
  , verifyTargetStrengtheningStageBundle
  )

-- | Target-level ways in which violating a realization validity condition can
-- widen Phil semantics. EXEC-012 pressures the first five constructors. The
-- capacity constructor is included so EXEC-013 can reuse the same relation
-- rather than introducing a second partiality algebra.
data TargetPartialityKind
  = TargetUndefinedBehavior
  | TargetPoison
  | TargetUnreachable
  | TargetTrap
  | TargetExceptionalHalt
  | TargetCapacityExhaustion Text
  | TargetOtherPartiality Text
  deriving (Eq, Ord, Show)

-- | Exact identity of one lower-level hazard. A target precondition and the
-- consequence of violating it are both semantic coordinates: changing either
-- one changes the relation that must be justified.
data RuntimePartialityHazardRef = RuntimePartialityHazardRef
  { runtimePartialityHazardPrecondition :: TargetPreconditionRef
  , runtimePartialityHazardKind :: TargetPartialityKind
  }
  deriving (Eq, Ord, Show)

newtype RuntimePartialitySourceOutcome = RuntimePartialitySourceOutcome
  { unRuntimePartialitySourceOutcome :: Text
  }
  deriving (Eq, Ord, Show)

newtype RuntimePartialityEnforcementKey = RuntimePartialityEnforcementKey
  { unRuntimePartialityEnforcementKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype RuntimePartialityAssumptionKey = RuntimePartialityAssumptionKey
  { unRuntimePartialityAssumptionKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype RuntimePartialityDeploymentRequirementKey =
  RuntimePartialityDeploymentRequirementKey
    { unRuntimePartialityDeploymentRequirementKey :: Text
    }
  deriving (Eq, Ord, Show)

-- | Target-independent ADR-026 disposition vocabulary. Storage allocation
-- failure already uses the same semantic alternatives in MEM-002/003; this
-- relation lifts them from allocation-only failure to arbitrary target validity
-- conditions. There is deliberately no "native target behavior" constructor.
data RuntimePartialityDisposition
  = RuntimePartialityMapsToSourceOutcome RuntimePartialitySourceOutcome
  | RuntimePartialityProvedSatisfied RevisionId
  | RuntimePartialityRuntimeEnforced RuntimePartialityEnforcementKey
  | RuntimePartialityAssumption RuntimePartialityAssumptionKey
  | RuntimePartialityDeploymentRequirement
      RuntimePartialityDeploymentRequirementKey
  deriving (Eq, Ord, Show)

-- | One exact realization partiality relation layered on SYS-014 target
-- strengthening. The target-strengthening stage already enumerates every target
-- precondition introduced by lowering and binds any retained derived obligation.
-- This layer classifies the hazardous ones and requires one explicit disposition
-- for every (precondition, consequence) pair.
data RuntimePartialityRelation = RuntimePartialityRelation
  { runtimePartialityTargetStage :: TargetStrengtheningStageBundle
  , runtimePartialityHazards :: Map TargetPreconditionRef (Set TargetPartialityKind)
  , runtimePartialitySourceOutcomes :: Set RuntimePartialitySourceOutcome
  , runtimePartialityDispositions
      :: Map RuntimePartialityHazardRef RuntimePartialityDisposition
  }
  deriving (Eq, Show)

newtype CheckedRuntimePartialityRelation = CheckedRuntimePartialityRelation
  { unCheckedRuntimePartialityRelation :: RuntimePartialityRelation
  }
  deriving (Eq, Show)

data RuntimePartialityError
  = RuntimePartialityTargetStageError TargetStrengtheningVerificationError
  | RuntimePartialityUnknownTargetPreconditions (Set TargetPreconditionRef)
  | RuntimePartialityEmptyHazardSet TargetPreconditionRef
  | RuntimePartialityEmptyHazardIdentity RuntimePartialityHazardRef
  | RuntimePartialityDispositionDomainMismatch
      (Set RuntimePartialityHazardRef)
      (Set RuntimePartialityHazardRef)
  | RuntimePartialityUndeclaredSourceOutcome
      RuntimePartialityHazardRef RuntimePartialitySourceOutcome
  | RuntimePartialityEmptySourceOutcome
      RuntimePartialityHazardRef RuntimePartialitySourceOutcome
  | RuntimePartialityUnknownAssuranceRevision
      RuntimePartialityHazardRef RevisionId
  | RuntimePartialityMissingRetainedObligation RuntimePartialityHazardRef
  | RuntimePartialityEmptyEnforcementKey RuntimePartialityHazardRef
  | RuntimePartialityEmptyAssumptionKey RuntimePartialityHazardRef
  | RuntimePartialityEmptyDeploymentRequirementKey RuntimePartialityHazardRef
  deriving (Eq, Show)

checkRuntimePartialityRelation
  :: RuntimePartialityRelation
  -> Either RuntimePartialityError CheckedRuntimePartialityRelation
checkRuntimePartialityRelation relation = do
  mapLeft RuntimePartialityTargetStageError $
    verifyTargetStrengtheningStageBundle (runtimePartialityTargetStage relation)

  let strengthenings = targetStrengtheningStageFacts
        (runtimePartialityTargetStage relation)
      knownPreconditions = Map.keysSet strengthenings
      classifiedPreconditions = Map.keysSet (runtimePartialityHazards relation)
      unknown = Set.difference classifiedPreconditions knownPreconditions
  if Set.null unknown
    then Right ()
    else Left (RuntimePartialityUnknownTargetPreconditions unknown)

  mapM_ checkHazardSet (Map.toAscList (runtimePartialityHazards relation))

  let expectedHazards = Set.fromList
        [ RuntimePartialityHazardRef precondition kind
        | (precondition, kinds) <- Map.toAscList (runtimePartialityHazards relation)
        , kind <- Set.toAscList kinds
        ]
      actualHazards = Map.keysSet (runtimePartialityDispositions relation)
  if expectedHazards == actualHazards
    then Right ()
    else Left (RuntimePartialityDispositionDomainMismatch
      expectedHazards actualHazards)

  mapM_ (checkDisposition relation strengthenings)
    (Map.toAscList (runtimePartialityDispositions relation))
  Right (CheckedRuntimePartialityRelation relation)

checkHazardSet
  :: (TargetPreconditionRef, Set TargetPartialityKind)
  -> Either RuntimePartialityError ()
checkHazardSet (precondition, kinds)
  | Set.null kinds = Left (RuntimePartialityEmptyHazardSet precondition)
  | otherwise = mapM_ checkKind (Set.toAscList kinds)
  where
    checkKind kind =
      let ref = RuntimePartialityHazardRef precondition kind
      in case kind of
          TargetCapacityExhaustion label
            | Text.null (Text.strip label) ->
                Left (RuntimePartialityEmptyHazardIdentity ref)
          TargetOtherPartiality label
            | Text.null (Text.strip label) ->
                Left (RuntimePartialityEmptyHazardIdentity ref)
          _ -> Right ()

checkDisposition
  :: RuntimePartialityRelation
  -> Map TargetPreconditionRef TargetStrengthening
  -> (RuntimePartialityHazardRef, RuntimePartialityDisposition)
  -> Either RuntimePartialityError ()
checkDisposition relation strengthenings (hazard, disposition) = do
  strengthening <- case Map.lookup
      (runtimePartialityHazardPrecondition hazard) strengthenings of
    Nothing -> Left (RuntimePartialityUnknownTargetPreconditions
      (Set.singleton (runtimePartialityHazardPrecondition hazard)))
    Just value -> Right value
  case disposition of
    RuntimePartialityMapsToSourceOutcome outcome -> do
      if Text.null (Text.strip (unRuntimePartialitySourceOutcome outcome))
        then Left (RuntimePartialityEmptySourceOutcome hazard outcome)
        else Right ()
      if Set.member outcome (runtimePartialitySourceOutcomes relation)
        then Right ()
        else Left (RuntimePartialityUndeclaredSourceOutcome hazard outcome)
    RuntimePartialityProvedSatisfied revision ->
      if Set.member revision (targetStrengtheningSourceAssurance strengthening)
        then Right ()
        else Left (RuntimePartialityUnknownAssuranceRevision hazard revision)
    RuntimePartialityRuntimeEnforced key -> do
      requireRetainedObligation hazard strengthening
      if Text.null (Text.strip (unRuntimePartialityEnforcementKey key))
        then Left (RuntimePartialityEmptyEnforcementKey hazard)
        else Right ()
    RuntimePartialityAssumption key -> do
      requireRetainedObligation hazard strengthening
      if Text.null (Text.strip (unRuntimePartialityAssumptionKey key))
        then Left (RuntimePartialityEmptyAssumptionKey hazard)
        else Right ()
    RuntimePartialityDeploymentRequirement key -> do
      requireRetainedObligation hazard strengthening
      if Text.null (Text.strip
          (unRuntimePartialityDeploymentRequirementKey key))
        then Left (RuntimePartialityEmptyDeploymentRequirementKey hazard)
        else Right ()

requireRetainedObligation
  :: RuntimePartialityHazardRef
  -> TargetStrengthening
  -> Either RuntimePartialityError ()
requireRetainedObligation hazard strengthening =
  case targetStrengtheningDerivedObligation strengthening of
    Just (RevisionId revision) | not (Text.null (Text.strip revision)) -> Right ()
    _ -> Left (RuntimePartialityMissingRetainedObligation hazard)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform = either (Left . transform) Right
