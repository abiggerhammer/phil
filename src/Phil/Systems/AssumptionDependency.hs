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
import qualified SystemsEvidencePreservationKernel as Kernel

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
makeAssumptionDependencyStageBundle base assumptions forward reverseDependencies = provisional
  { assumptionDependencyStageRevision =
      deriveAssumptionDependencyStageRevision provisional }
  where
    provisional = AssumptionDependencyStageBundle
      { assumptionDependencyStageBase = base
      , assumptionDependencyStageRevision = AssumptionDependencyStageRevision "pending"
      , assumptionDependencyStageAssumptions = assumptions
      , assumptionDependencyStageForward = forward
      , assumptionDependencyStageReverse = reverseDependencies
      }

verifyAssumptionDependencyStageBundle
  :: AssumptionDependencyStageBundle
  -> Either AssumptionDependencyVerificationError ()
verifyAssumptionDependencyStageBundle bundle = do
  let baseResult = verifyEvidenceErasureStageBundle (assumptionDependencyStageBase bundle)
  case Kernel.decideSystemsEvidenceByFacts
      Kernel.True (toKernelBool (isRight baseResult)) Kernel.True of
    Kernel.SystemsEvidenceAcceptedDecision ->
      mapLeft AssumptionDependencyBaseError baseResult
    Kernel.SystemsEvidenceErasureDecision ->
      mapLeft AssumptionDependencyBaseError baseResult
    _ -> kernelInvariant "cumulative-erasure-predecessor"
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

  case Kernel.decideAssumptionDependencyByFacts
      (toKernelBool (requiredAssumptions == actualAssumptions))
      Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True of
    Kernel.AssumptionDependencyAcceptedDecision -> Right ()
    Kernel.AssumptionRegistryDecision ->
      Left (AssumptionRegistryDomainMismatch requiredAssumptions actualAssumptions)
    _ -> kernelInvariant "assumption-registry"
  case Kernel.decideAssumptionDependencyByFacts
      Kernel.True Kernel.True Kernel.True
      (toKernelBool (requiredConsumers == actualConsumers))
      Kernel.True Kernel.True of
    Kernel.AssumptionDependencyAcceptedDecision -> Right ()
    Kernel.AssumptionForwardDecision ->
      Left (AssumptionForwardDomainMismatch requiredConsumers actualConsumers)
    _ -> kernelInvariant "assumption-forward-domain"
  mapM_ (checkForward bundle) (Map.toAscList required)

  let expectedReverse = deriveReverse required
      actualReverse = assumptionDependencyStageReverse bundle
      expectedReverseDomain = Map.keysSet expectedReverse
      actualReverseDomain = Map.keysSet actualReverse
  case Kernel.decideAssumptionDependencyByFacts
      Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True
      (toKernelBool (expectedReverseDomain == actualReverseDomain)) of
    Kernel.AssumptionDependencyAcceptedDecision -> Right ()
    Kernel.AssumptionReverseDecision ->
      Left (AssumptionReverseDomainMismatch expectedReverseDomain actualReverseDomain)
    _ -> kernelInvariant "assumption-reverse-domain"
  mapM_ (checkReverse actualReverse) (Map.toAscList expectedReverse)
  case Kernel.decideSystemsEvidenceByFacts Kernel.True Kernel.True Kernel.True of
    Kernel.SystemsEvidenceAcceptedDecision -> Right ()
    _ -> kernelInvariant "cumulative-acceptance"

checkBinding
  :: (StageAssumptionKey, AssumptionBinding)
  -> Either AssumptionDependencyVerificationError ()
checkBinding (key, binding) = do
  requireEqual AssumptionBindingMapKeyMismatch key (assumptionBindingKey binding)
  if Text.null (unStageAssumptionKey key)
    then Left AssumptionBindingEmptyKey
    else Right ()
  let validityScopePresent = case assumptionBindingValidityScope binding of
        AssumptionValidityScopeRevision value -> not (Text.null value)
  case Kernel.decideAssumptionDependencyByFacts
      Kernel.True Kernel.True (toKernelBool validityScopePresent)
      Kernel.True Kernel.True Kernel.True of
    Kernel.AssumptionDependencyAcceptedDecision -> Right ()
    Kernel.AssumptionValidityScopeDecision ->
      Left (AssumptionBindingEmptyValidityScope key)
    _ -> kernelInvariant "assumption-validity-scope"

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
  case Kernel.decideAssumptionDependencyByFacts
      Kernel.True Kernel.True Kernel.True
      (toKernelBool (expectedAssumptions == actualAssumptions))
      Kernel.True Kernel.True of
    Kernel.AssumptionDependencyAcceptedDecision -> Right ()
    Kernel.AssumptionForwardDecision ->
      Left (AssumptionForwardSetMismatch consumer expectedAssumptions actualAssumptions)
    _ -> kernelInvariant "assumption-forward-set"
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
      case Kernel.decideAssumptionDependencyByFacts
          Kernel.True Kernel.True Kernel.True Kernel.True
          (toKernelBool (expectedScope == actualScope)) Kernel.True of
        Kernel.AssumptionDependencyAcceptedDecision -> Right ()
        Kernel.AssumptionForwardScopeDecision -> Left
          (AssumptionForwardScopeMismatch consumer assumption expectedScope actualScope)
        _ -> kernelInvariant "assumption-forward-scope"

checkReverse
  :: Map StageAssumptionKey (Set AssumptionConsumer)
  -> (StageAssumptionKey, Set AssumptionConsumer)
  -> Either AssumptionDependencyVerificationError ()
checkReverse actualReverse (assumption, expectedConsumers) =
  case Map.lookup assumption actualReverse of
    Nothing -> Left (AssumptionReverseDomainMismatch
      (Set.singleton assumption) (Map.keysSet actualReverse))
    Just actualConsumers ->
      case Kernel.decideAssumptionDependencyByFacts
          Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True
          (toKernelBool (expectedConsumers == actualConsumers)) of
        Kernel.AssumptionDependencyAcceptedDecision -> Right ()
        Kernel.AssumptionReverseDecision -> Left
          (AssumptionReverseConsumerMismatch assumption expectedConsumers actualConsumers)
        _ -> kernelInvariant "assumption-reverse-consumers"

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

toKernelBool :: Bool -> Kernel.Bool
toKernelBool value = if value then Kernel.True else Kernel.False

isRight :: Either a b -> Bool
isRight value = case value of
  Right _ -> True
  Left _ -> False

kernelInvariant :: String -> Either e a
kernelInvariant label =
  error ("SystemsEvidencePreservationKernel mismatch: " <> label)
