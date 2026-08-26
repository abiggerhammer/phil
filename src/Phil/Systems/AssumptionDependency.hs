{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.AssumptionDependency
  ( AssumptionDependencyStageRevision (..)
  , StageAssumptionKey (..)
  , AssumptionValidityScopeRevision (..)
  , AssumptionBinding (..)
  , AssumptionConsumer (..)
  , AssumptionDependencyStageBundle (..)
  , AssumptionDependencyVerificationError (..)
  , deriveRequiredAssumptionConsumers
  , deriveAssumptionDependencyStageRevision
  , makeAssumptionDependencyStageBundle
  , verifyAssumptionDependencyStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.EvidenceErasure
  ( EvidenceErasureStageBundle (..)
  , EvidenceErasureStageRevision (..)
  , EvidenceErasureVerificationError
  , ErasureJustification (..)
  , ErasureJustificationKey (..)
  , verifyEvidenceErasureStageBundle
  )
import Phil.Systems.EvidenceSubjectTransfer
  ( EvidenceTransferStageBundle (..)
  )
import Phil.Systems.Phase1Stage
  ( Phase1FactDisposition (..)
  , Phase1StageBundle (..)
  , SourceFactKey (..)
  , SystemsJustification (..)
  , SystemsMechanismKey (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )

newtype AssumptionDependencyStageRevision = AssumptionDependencyStageRevision
  { unAssumptionDependencyStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype StageAssumptionKey = StageAssumptionKey
  { unStageAssumptionKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype AssumptionValidityScopeRevision = AssumptionValidityScopeRevision
  { unAssumptionValidityScopeRevision :: Text
  }
  deriving (Eq, Ord, Show)

data AssumptionBinding = AssumptionBinding
  { assumptionBindingKey :: StageAssumptionKey
  , assumptionBindingValidityScope :: AssumptionValidityScopeRevision
  }
  deriving (Eq, Ord, Show)

data AssumptionConsumer
  = AssumptionFactConsumer SourceFactKey
  | AssumptionMechanismConsumer SystemsMechanismKey
  | AssumptionErasureConsumer ErasureJustificationKey
  deriving (Eq, Ord, Show)

-- | SYS-013 keeps assumption lineage bidirectional. Forward dependencies say
-- which exact assumptions each fact/mechanism/erasure consumes. Reverse
-- dependencies say which exact consumers remain downstream of each assumption.
-- Both sides carry the registry's exact validity-scope revision.
data AssumptionDependencyStageBundle = AssumptionDependencyStageBundle
  { assumptionDependencyStageBase :: EvidenceErasureStageBundle
  , assumptionDependencyStageRevision :: AssumptionDependencyStageRevision
  , assumptionDependencyStageAssumptions :: Map StageAssumptionKey AssumptionBinding
  , assumptionDependencyStageForward
      :: Map AssumptionConsumer (Map StageAssumptionKey AssumptionValidityScopeRevision)
  , assumptionDependencyStageReverse
      :: Map StageAssumptionKey (Set AssumptionConsumer)
  }
  deriving (Eq, Show)

data AssumptionDependencyVerificationError
  = AssumptionDependencyBaseError EvidenceErasureVerificationError
  | AssumptionDependencyStageRevisionMismatch
      AssumptionDependencyStageRevision AssumptionDependencyStageRevision
  | AssumptionBindingMapKeyMismatch StageAssumptionKey StageAssumptionKey
  | AssumptionBindingEmptyKey
  | AssumptionBindingEmptyValidityScope StageAssumptionKey
  | AssumptionRegistryDomainMismatch
      (Set StageAssumptionKey) (Set StageAssumptionKey)
  | AssumptionForwardDomainMismatch
      (Set AssumptionConsumer) (Set AssumptionConsumer)
  | AssumptionForwardSetMismatch
      AssumptionConsumer (Set StageAssumptionKey) (Set StageAssumptionKey)
  | AssumptionForwardScopeMismatch
      AssumptionConsumer
      StageAssumptionKey
      AssumptionValidityScopeRevision
      AssumptionValidityScopeRevision
  | AssumptionReverseDomainMismatch
      (Set StageAssumptionKey) (Set StageAssumptionKey)
  | AssumptionReverseConsumerMismatch
      StageAssumptionKey (Set AssumptionConsumer) (Set AssumptionConsumer)
  deriving (Eq, Show)

deriveRequiredAssumptionConsumers
  :: EvidenceErasureStageBundle
  -> Map AssumptionConsumer (Set StageAssumptionKey)
deriveRequiredAssumptionConsumers bundle = Map.fromList
  (factConsumers <> mechanismConsumers <> erasureConsumers)
  where
    phase1 = basePhase1Stage bundle
    dispositions = phase1StageFactDispositions phase1

    factConsumers =
      [ (AssumptionFactConsumer fact, Set.map StageAssumptionKey assumptions)
      | (fact, disposition) <- Map.toAscList dispositions
      , let assumptions = factAssumptionRefs disposition
      , not (Set.null assumptions)
      ]

    mechanismConsumers =
      [ (AssumptionMechanismConsumer mechanism, Set.map StageAssumptionKey assumptions)
      | (mechanism, justification) <-
          Map.toAscList (phase1StageSystemsJustifications phase1)
      , let assumptions = systemsJustificationAssumptionRefs justification
      , not (Set.null assumptions)
      ]

    erasureConsumers =
      [ (AssumptionErasureConsumer key, Set.map StageAssumptionKey assumptions)
      | (key, erasure) <-
          Map.toAscList (evidenceErasureStageJustifications bundle)
      , Just disposition <- [Map.lookup (erasureSourceFact erasure) dispositions]
      , let assumptions = factAssumptionRefs disposition
      , not (Set.null assumptions)
      ]

deriveAssumptionDependencyStageRevision
  :: AssumptionDependencyStageBundle
  -> AssumptionDependencyStageRevision
deriveAssumptionDependencyStageRevision bundle = AssumptionDependencyStageRevision
  ("phil.phase1.stage.assumption-dependency.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom (baseRevisionText (assumptionDependencyStageBase bundle)))
      , ("assumptions", SemanticRecord (Map.fromList
          [ (unStageAssumptionKey key, semanticBinding binding)
          | (key, binding) <- Map.toAscList
              (assumptionDependencyStageAssumptions bundle)
          ]))
      , ("forward", SemanticRecord (Map.fromList
          [ (consumerText consumer, semanticScopedAssumptions dependencies)
          | (consumer, dependencies) <- Map.toAscList
              (assumptionDependencyStageForward bundle)
          ]))
      , ("reverse", SemanticRecord (Map.fromList
          [ (unStageAssumptionKey assumption, SemanticUnordered
              (Set.map (SemanticAtom . consumerText) consumers))
          | (assumption, consumers) <- Map.toAscList
              (assumptionDependencyStageReverse bundle)
          ]))
      ])))

makeAssumptionDependencyStageBundle
  :: EvidenceErasureStageBundle
  -> Map StageAssumptionKey AssumptionBinding
  -> Map AssumptionConsumer (Map StageAssumptionKey AssumptionValidityScopeRevision)
  -> Map StageAssumptionKey (Set AssumptionConsumer)
  -> AssumptionDependencyStageBundle
makeAssumptionDependencyStageBundle base assumptions forward reverse = provisional
  { assumptionDependencyStageRevision =
      deriveAssumptionDependencyStageRevision provisional }
  where
    provisional = AssumptionDependencyStageBundle
      { assumptionDependencyStageBase = base
      , assumptionDependencyStageRevision = AssumptionDependencyStageRevision "pending"
      , assumptionDependencyStageAssumptions = assumptions
      , assumptionDependencyStageForward = forward
      , assumptionDependencyStageReverse = reverse
      }

verifyAssumptionDependencyStageBundle
  :: AssumptionDependencyStageBundle
  -> Either AssumptionDependencyVerificationError ()
verifyAssumptionDependencyStageBundle bundle = do
  mapLeft AssumptionDependencyBaseError $
    verifyEvidenceErasureStageBundle (assumptionDependencyStageBase bundle)
  requireEqual AssumptionDependencyStageRevisionMismatch
    (deriveAssumptionDependencyStageRevision bundle)
    (assumptionDependencyStageRevision bundle)
  mapM_ checkBinding
    (Map.toAscList (assumptionDependencyStageAssumptions bundle))

  let required = deriveRequiredAssumptionConsumers
        (assumptionDependencyStageBase bundle)
      requiredAssumptions = Set.unions (Map.elems required)
      actualAssumptions = Map.keysSet (assumptionDependencyStageAssumptions bundle)
      requiredConsumers = Map.keysSet required
      actualConsumers = Map.keysSet (assumptionDependencyStageForward bundle)

  requireEqual AssumptionRegistryDomainMismatch
    requiredAssumptions actualAssumptions
  requireEqual AssumptionForwardDomainMismatch
    requiredConsumers actualConsumers
  mapM_ (checkForward bundle) (Map.toAscList required)

  let expectedReverse = deriveReverse required
      actualReverse = assumptionDependencyStageReverse bundle
  requireEqual AssumptionReverseDomainMismatch
    (Map.keysSet expectedReverse) (Map.keysSet actualReverse)
  mapM_ (checkReverse actualReverse) (Map.toAscList expectedReverse)

checkBinding
  :: (StageAssumptionKey, AssumptionBinding)
  -> Either AssumptionDependencyVerificationError ()
checkBinding (key, binding) = do
  requireEqual AssumptionBindingMapKeyMismatch key (assumptionBindingKey binding)
  if Text.null (unStageAssumptionKey key)
    then Left AssumptionBindingEmptyKey
    else Right ()
  case assumptionBindingValidityScope binding of
    AssumptionValidityScopeRevision value
      | Text.null value -> Left (AssumptionBindingEmptyValidityScope key)
      | otherwise -> Right ()

checkForward
  :: AssumptionDependencyStageBundle
  -> (AssumptionConsumer, Set StageAssumptionKey)
  -> Either AssumptionDependencyVerificationError ()
checkForward bundle (consumer, expectedAssumptions) = do
  actualDependencies <- case Map.lookup consumer (assumptionDependencyStageForward bundle) of
    Nothing -> Left (AssumptionForwardDomainMismatch
      (Set.singleton consumer) Set.empty)
    Just value -> Right value
  let actualAssumptions = Map.keysSet actualDependencies
  requireEqual (AssumptionForwardSetMismatch consumer)
    expectedAssumptions actualAssumptions
  mapM_ (checkScope actualDependencies) (Set.toAscList expectedAssumptions)
  where
    registry = assumptionDependencyStageAssumptions bundle
    checkScope dependencies assumption = do
      expectedScope <- case Map.lookup assumption registry of
        Nothing -> Left (AssumptionRegistryDomainMismatch
          (Set.singleton assumption) (Map.keysSet registry))
        Just binding -> Right (assumptionBindingValidityScope binding)
      actualScope <- case Map.lookup assumption dependencies of
        Nothing -> Left (AssumptionForwardSetMismatch consumer
          expectedAssumptions (Map.keysSet dependencies))
        Just scope -> Right scope
      requireEqual (AssumptionForwardScopeMismatch consumer assumption)
        expectedScope actualScope

checkReverse
  :: Map StageAssumptionKey (Set AssumptionConsumer)
  -> (StageAssumptionKey, Set AssumptionConsumer)
  -> Either AssumptionDependencyVerificationError ()
checkReverse actualReverse (assumption, expectedConsumers) =
  case Map.lookup assumption actualReverse of
    Nothing -> Left (AssumptionReverseDomainMismatch
      (Set.singleton assumption) (Map.keysSet actualReverse))
    Just actualConsumers -> requireEqual
      (AssumptionReverseConsumerMismatch assumption)
      expectedConsumers actualConsumers

factAssumptionRefs :: Phase1FactDisposition -> Set Text
factAssumptionRefs disposition = case disposition of
  Phase1FactRealized _ -> Set.empty
  Phase1FactPreserved _ -> Set.empty
  Phase1FactExported _ -> Set.empty
  Phase1FactAssumptionDependent assumptions inner ->
    Set.union assumptions (factAssumptionRefs inner)

deriveReverse
  :: Map AssumptionConsumer (Set StageAssumptionKey)
  -> Map StageAssumptionKey (Set AssumptionConsumer)
deriveReverse required = Map.fromListWith Set.union
  [ (assumption, Set.singleton consumer)
  | (consumer, assumptions) <- Map.toAscList required
  , assumption <- Set.toAscList assumptions
  ]

basePhase1Stage :: EvidenceErasureStageBundle -> Phase1StageBundle
basePhase1Stage =
  subjectStageBase
    . evidenceTransferStageBase
    . evidenceErasureStageBase

baseRevisionText :: EvidenceErasureStageBundle -> Text
baseRevisionText =
  unEvidenceErasureStageRevision . evidenceErasureStageRevision

semanticBinding :: AssumptionBinding -> SemanticForm
semanticBinding binding = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom
      (unStageAssumptionKey (assumptionBindingKey binding)))
  , ("validity_scope", SemanticAtom
      (unAssumptionValidityScopeRevision
        (assumptionBindingValidityScope binding)))
  ])

semanticScopedAssumptions
  :: Map StageAssumptionKey AssumptionValidityScopeRevision
  -> SemanticForm
semanticScopedAssumptions dependencies = SemanticRecord (Map.fromList
  [ (unStageAssumptionKey key, SemanticAtom
      (unAssumptionValidityScopeRevision scope))
  | (key, scope) <- Map.toAscList dependencies
  ])

consumerText :: AssumptionConsumer -> Text
consumerText consumer = case consumer of
  AssumptionFactConsumer fact ->
    "fact:" <> unSourceFactKey fact
  AssumptionMechanismConsumer mechanism ->
    "mechanism:" <> unSystemsMechanismKey mechanism
  AssumptionErasureConsumer erasure ->
    "erasure:" <> unErasureJustificationKey erasure

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
