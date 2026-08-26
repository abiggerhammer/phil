{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.AssumptionDependencyWitnesses
  ( uploadAssumptionDependencyStage
  , steveAssumptionDependencyStage
  , steveAssumptionRegistry
  , completeAssumptionDependencyStage
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Examples.Phase1.EvidenceErasureWitnesses
  ( steveErasureAfterDischarge
  , uploadErasureAfterDischarge
  )
import Phil.Systems.AssumptionDependency
import Phil.Systems.EvidenceErasure
  ( EvidenceErasureStageBundle
  )

uploadAssumptionDependencyStage :: AssumptionDependencyStageBundle
uploadAssumptionDependencyStage =
  completeAssumptionDependencyStage uploadErasureAfterDischarge Map.empty

steveAssumptionDependencyStage :: Either String AssumptionDependencyStageBundle
steveAssumptionDependencyStage = do
  base <- steveErasureAfterDischarge
  pure (completeAssumptionDependencyStage base (steveAssumptionRegistry base))

steveAssumptionRegistry
  :: EvidenceErasureStageBundle
  -> Map StageAssumptionKey AssumptionBinding
steveAssumptionRegistry base = Map.fromSet binding requiredAssumptions
  where
    requiredAssumptions = Set.unions
      (Map.elems (deriveRequiredAssumptionConsumers base))
    binding key = AssumptionBinding
      { assumptionBindingKey = key
      , assumptionBindingValidityScope = scopeFor key
      }

completeAssumptionDependencyStage
  :: EvidenceErasureStageBundle
  -> Map StageAssumptionKey AssumptionBinding
  -> AssumptionDependencyStageBundle
completeAssumptionDependencyStage base registry =
  makeAssumptionDependencyStageBundle base registry forward reverseDependencies
  where
    required = deriveRequiredAssumptionConsumers base
    forward = Map.map (Map.fromSet scopeFor) required
    reverseDependencies = deriveReverse required

scopeFor :: StageAssumptionKey -> AssumptionValidityScopeRevision
scopeFor key = AssumptionValidityScopeRevision
  ("scope.phase1.systems.assumption."
    <> unStageAssumptionKey key
    <> ".v1")

deriveReverse
  :: Map AssumptionConsumer (Set StageAssumptionKey)
  -> Map StageAssumptionKey (Set AssumptionConsumer)
deriveReverse required = Map.fromListWith Set.union
  [ (assumption, Set.singleton consumer)
  | (consumer, assumptions) <- Map.toAscList required
  , assumption <- Set.toAscList assumptions
  ]
