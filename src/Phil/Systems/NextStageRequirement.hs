{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.NextStageRequirement
  ( NextStageRequirementStageRevision (..)
  , NextStageRequirementRevision (..)
  , NextStageValidityScope (..)
  , NextStageRequirementBasis (..)
  , NextStageSourceRef (..)
  , NextStageRequirement (..)
  , NextStageRequirementStageBundle (..)
  , NextStageRequirementVerificationError (..)
  , deriveExpectedNextStageRequirements
  , deriveNextStageRequirementRevision
  , deriveNextStageRequirementStageRevision
  , makeNextStageRequirementStageBundle
  , completeNextStageRequirementStageBundle
  , verifyNextStageRequirementStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (RevisionId (..))
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.CostAttribution
  ( CostAttributionStageBundle (..)
  , CostAttributionStageRevision (..)
  , CostAttributionVerificationError
  , CostChargeIdentity (..)
  , RuntimeCostBasis (..)
  , verifyCostAttributionStageBundle
  )
import Phil.Systems.IR
  ( BlockId (..)
  , DecisionId (..)
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeClaimStageBundle (..)
  , RuntimeSiteKey (..)
  , RuntimeSiteSlot (..)
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  , RuntimePrimitiveStageBundle (..)
  )
import Phil.Systems.StagingEffect
  ( StagingEffectStageBundle (..)
  )
import Phil.Systems.TargetStrengthening
  ( TargetPreconditionRef (..)
  , TargetStrengthening (..)
  , TargetStrengtheningStageBundle (..)
  )

newtype NextStageRequirementStageRevision = NextStageRequirementStageRevision
  { unNextStageRequirementStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype NextStageRequirementRevision = NextStageRequirementRevision
  { unNextStageRequirementRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype NextStageValidityScope = NextStageValidityScope
  { unNextStageValidityScope :: Text
  }
  deriving (Eq, Ord, Show)

-- | The exact Systems fact that makes a next-stage requirement mandatory.
-- SYS-019 currently has two mechanically enumerable sources: target facts
-- introduced by lowering and reusable runtime primitive/profile selections.
data NextStageRequirementBasis
  = NextStageTargetPreconditionBasis TargetPreconditionRef
  | NextStageRuntimePrimitiveBasis RuntimePrimitiveProfileRef
  deriving (Eq, Ord, Show)

-- | Exact provenance retained on the competence-boundary export.  These are
-- deliberately not backend symbols or ambient ABI names.
data NextStageSourceRef
  = NextStageTargetPreconditionSource TargetPreconditionRef
  | NextStageRuntimePrimitiveSource RuntimePrimitiveProfileRef
  | NextStageRuntimeSiteSource RuntimeSiteKey
  | NextStageSemanticSubjectSource Text
  | NextStageSourceAssurance RevisionId
  | NextStageDerivedObligationSource RevisionId
  | NextStageCostChargeSource CostChargeIdentity
  deriving (Eq, Ord, Show)

data NextStageRequirement = NextStageRequirement
  { nextStageRequirementRevision :: NextStageRequirementRevision
  , nextStageRequirementBasis :: NextStageRequirementBasis
  , nextStageRequirementSourceSystemsRefs :: Set NextStageSourceRef
  , nextStageRequirementRequiredFactOrContract :: Text
  , nextStageRequirementAcceptanceRule :: Text
  , nextStageRequirementValidityScope :: NextStageValidityScope
  }
  deriving (Eq, Ord, Show)

data NextStageRequirementStageBundle = NextStageRequirementStageBundle
  { nextStageRequirementStageBase :: CostAttributionStageBundle
  , nextStageRequirementStageRevision :: NextStageRequirementStageRevision
  , nextStageRequirementStageRequirements
      :: Map NextStageRequirementRevision NextStageRequirement
  }
  deriving (Eq, Show)

data NextStageRequirementVerificationError
  = NextStageRequirementBaseError CostAttributionVerificationError
  | NextStageRequirementStageRevisionMismatch
      NextStageRequirementStageRevision NextStageRequirementStageRevision
  | NextStageRequirementRevisionCollision (Set NextStageRequirementRevision)
  | NextStageRequirementDomainMismatch
      (Set NextStageRequirementRevision) (Set NextStageRequirementRevision)
  | NextStageRequirementBasisDomainMismatch
      (Set NextStageRequirementBasis) (Set NextStageRequirementBasis)
  | NextStageRequirementDuplicateBasis NextStageRequirementBasis
  | NextStageRequirementMapKeyMismatch
      NextStageRequirementRevision NextStageRequirementRevision
  | NextStageRequirementRevisionMismatch
      NextStageRequirementRevision NextStageRequirementRevision
  | NextStageRequirementEmptyRevision NextStageRequirementBasis
  | NextStageRequirementEmptySourceRefs NextStageRequirementBasis
  | NextStageRequirementEmptyFact NextStageRequirementBasis
  | NextStageRequirementFolkloreOnly NextStageRequirementBasis Text
  | NextStageRequirementEmptyAcceptanceRule NextStageRequirementBasis
  | NextStageRequirementEmptyValidityScope NextStageRequirementBasis
  | NextStageRequirementEntryMismatch
      NextStageRequirementRevision NextStageRequirement NextStageRequirement
  deriving (Eq, Show)

deriveExpectedNextStageRequirements
  :: CostAttributionStageBundle
  -> Either NextStageRequirementVerificationError
       (Map NextStageRequirementRevision NextStageRequirement)
deriveExpectedNextStageRequirements base =
  if Map.size result == length pairs
    then Right result
    else Left (NextStageRequirementRevisionCollision
      (duplicateKeys (map fst pairs)))
  where
    primitiveStage = stagingEffectStageBase
      (costAttributionStageBase base)
    targetStage = runtimeClaimStageBase
      (runtimePrimitiveStageBase primitiveStage)

    targetPairs =
      [ requirementPair (targetRequirement base strengthening)
      | (_, strengthening) <- Map.toAscList
          (targetStrengtheningStageFacts targetStage)
      ]

    runtimePairs =
      [ requirementPair (runtimeRequirement base primitiveStage profile sites)
      | (profile, sites) <- Map.toAscList
          (runtimePrimitiveStageReverse primitiveStage)
      ]

    pairs = targetPairs <> runtimePairs
    result = Map.fromList pairs

    requirementPair requirement =
      (nextStageRequirementRevision requirement, requirement)

deriveNextStageRequirementRevision
  :: NextStageRequirement
  -> NextStageRequirementRevision
deriveNextStageRequirementRevision requirement = NextStageRequirementRevision
  ("phil.phase1.next-stage.requirement.canonical.v1:"
    <> canonicalSemanticForm (semanticRequirementBody requirement))

deriveNextStageRequirementStageRevision
  :: NextStageRequirementStageBundle
  -> NextStageRequirementStageRevision
deriveNextStageRequirementStageRevision bundle =
  NextStageRequirementStageRevision
    ("phil.phase1.stage.next-stage-requirements.canonical.v1:"
      <> canonicalSemanticForm (SemanticRecord (Map.fromList
        [ ("base_stage", SemanticAtom
            (unCostAttributionStageRevision
              (costAttributionStageRevision
                (nextStageRequirementStageBase bundle))))
        , ("requirements", SemanticUnordered (Set.fromList
            [ semanticRequirement requirement
            | (_, requirement) <- Map.toAscList
                (nextStageRequirementStageRequirements bundle)
            ]))
        ])))

makeNextStageRequirementStageBundle
  :: CostAttributionStageBundle
  -> Map NextStageRequirementRevision NextStageRequirement
  -> NextStageRequirementStageBundle
makeNextStageRequirementStageBundle base requirements = provisional
  { nextStageRequirementStageRevision =
      deriveNextStageRequirementStageRevision provisional
  }
  where
    provisional = NextStageRequirementStageBundle
      { nextStageRequirementStageBase = base
      , nextStageRequirementStageRevision =
          NextStageRequirementStageRevision "pending"
      , nextStageRequirementStageRequirements = requirements
      }

completeNextStageRequirementStageBundle
  :: CostAttributionStageBundle
  -> Either String NextStageRequirementStageBundle
completeNextStageRequirementStageBundle base = do
  requirements <- mapLeft show
    (deriveExpectedNextStageRequirements base)
  pure (makeNextStageRequirementStageBundle base requirements)

verifyNextStageRequirementStageBundle
  :: NextStageRequirementStageBundle
  -> Either NextStageRequirementVerificationError ()
verifyNextStageRequirementStageBundle bundle = do
  mapLeft NextStageRequirementBaseError $
    verifyCostAttributionStageBundle
      (nextStageRequirementStageBase bundle)
  requireEqual NextStageRequirementStageRevisionMismatch
    (deriveNextStageRequirementStageRevision bundle)
    (nextStageRequirementStageRevision bundle)

  expected <- deriveExpectedNextStageRequirements
    (nextStageRequirementStageBase bundle)
  let actual = nextStageRequirementStageRequirements bundle
      expectedDomain = Map.keysSet expected
      actualDomain = Map.keysSet actual
      expectedBases = Set.fromList
        (map nextStageRequirementBasis (Map.elems expected))
      actualBasisList = map nextStageRequirementBasis (Map.elems actual)
      actualBases = Set.fromList actualBasisList

  requireEqual NextStageRequirementDomainMismatch
    expectedDomain actualDomain
  case duplicateKeys actualBasisList of
    duplicates | Set.null duplicates -> Right ()
               | otherwise -> Left
                   (NextStageRequirementDuplicateBasis
                     (Set.findMin duplicates))
  requireEqual NextStageRequirementBasisDomainMismatch
    expectedBases actualBases
  mapM_ (checkRequirement actual) (Map.toAscList expected)

checkRequirement
  :: Map NextStageRequirementRevision NextStageRequirement
  -> (NextStageRequirementRevision, NextStageRequirement)
  -> Either NextStageRequirementVerificationError ()
checkRequirement actual (revision, expected) = do
  observed <- maybe
    (Left (NextStageRequirementDomainMismatch
      (Set.singleton revision) (Map.keysSet actual)))
    Right
    (Map.lookup revision actual)
  let basis = nextStageRequirementBasis observed
  requireEqual NextStageRequirementMapKeyMismatch
    revision (nextStageRequirementRevision observed)
  if Text.null (unNextStageRequirementRevision
      (nextStageRequirementRevision observed))
    then Left (NextStageRequirementEmptyRevision basis)
    else Right ()
  requireEqual NextStageRequirementRevisionMismatch
    revision (deriveNextStageRequirementRevision observed)
  if Set.null (nextStageRequirementSourceSystemsRefs observed)
    then Left (NextStageRequirementEmptySourceRefs basis)
    else Right ()
  if Text.null (Text.strip
      (nextStageRequirementRequiredFactOrContract observed))
    then Left (NextStageRequirementEmptyFact basis)
    else Right ()
  if folkloreOnly (nextStageRequirementRequiredFactOrContract observed)
    then Left (NextStageRequirementFolkloreOnly basis
      (nextStageRequirementRequiredFactOrContract observed))
    else Right ()
  if Text.null (Text.strip (nextStageRequirementAcceptanceRule observed))
    then Left (NextStageRequirementEmptyAcceptanceRule basis)
    else Right ()
  if Text.null (Text.strip (unNextStageValidityScope
      (nextStageRequirementValidityScope observed)))
    then Left (NextStageRequirementEmptyValidityScope basis)
    else Right ()
  if observed == expected
    then Right ()
    else Left (NextStageRequirementEntryMismatch revision expected observed)

targetRequirement
  :: CostAttributionStageBundle
  -> TargetStrengthening
  -> NextStageRequirement
targetRequirement base strengthening = seal provisional
  where
    ref = targetStrengtheningRef strengthening
    sourceRefs = Set.unions
      [ Set.singleton (NextStageTargetPreconditionSource ref)
      , Set.map NextStageSemanticSubjectSource
          (targetStrengtheningSemanticSubjects strengthening)
      , Set.map NextStageSourceAssurance
          (targetStrengtheningSourceAssurance strengthening)
      , maybe Set.empty
          (Set.singleton . NextStageDerivedObligationSource)
          (targetStrengtheningDerivedObligation strengthening)
      ]
    provisional = NextStageRequirement
      { nextStageRequirementRevision =
          NextStageRequirementRevision "pending"
      , nextStageRequirementBasis =
          NextStageTargetPreconditionBasis ref
      , nextStageRequirementSourceSystemsRefs = sourceRefs
      , nextStageRequirementRequiredFactOrContract =
          targetPreconditionRequirement ref
      , nextStageRequirementAcceptanceRule =
          "the next-stage verifier must establish this exact target precondition for the selected ABI/layout/runtime realization, or retain its exact obligation before target emission; ambient native-ABI convention is not evidence"
      , nextStageRequirementValidityScope = NextStageValidityScope
          (baseScope base <> ";decision="
            <> unDecisionId (targetPreconditionDecision ref))
      }

runtimeRequirement
  :: CostAttributionStageBundle
  -> RuntimePrimitiveStageBundle
  -> RuntimePrimitiveProfileRef
  -> Set RuntimeSiteKey
  -> NextStageRequirement
runtimeRequirement base _ profile sites = seal provisional
  where
    chargeRef = case Map.lookup profile
        (costAttributionStageRuntimeBases base) of
      Just basis -> Set.singleton
        (NextStageCostChargeSource (runtimeCostBasisCharge basis))
      Nothing -> Set.empty
    sourceRefs = Set.unions
      [ Set.singleton (NextStageRuntimePrimitiveSource profile)
      , Set.map NextStageRuntimeSiteSource sites
      , chargeRef
      ]
    provisional = NextStageRequirement
      { nextStageRequirementRevision =
          NextStageRequirementRevision "pending"
      , nextStageRequirementBasis =
          NextStageRuntimePrimitiveBasis profile
      , nextStageRequirementSourceSystemsRefs = sourceRefs
      , nextStageRequirementRequiredFactOrContract =
          "backend lowering provides an exact ABI/signature/runtime mapping for primitive profile "
            <> unRuntimePrimitiveProfileRef profile
            <> " at every bound runtime site"
      , nextStageRequirementAcceptanceRule =
          "the next-stage verifier must bind this exact primitive profile to a concrete target ABI/signature/calling-convention/runtime realization for every named site; symbol coincidence, platform defaults, and ambient native-ABI inference are insufficient"
      , nextStageRequirementValidityScope =
          NextStageValidityScope (baseScope base <> ";runtime-profile="
            <> unRuntimePrimitiveProfileRef profile)
      }

seal :: NextStageRequirement -> NextStageRequirement
seal provisional = provisional
  { nextStageRequirementRevision =
      deriveNextStageRequirementRevision provisional }

baseScope :: CostAttributionStageBundle -> Text
baseScope base = "cost-attribution-stage="
  <> unCostAttributionStageRevision (costAttributionStageRevision base)

folkloreOnly :: Text -> Bool
folkloreOnly value = Text.toCaseFold (Text.strip value) `Set.member`
  Set.fromList
    [ "native abi"
    , "platform default"
    , "target default"
    , "compiler default"
    , "host default"
    ]

semanticRequirement :: NextStageRequirement -> SemanticForm
semanticRequirement requirement = SemanticRecord (Map.fromList
  [ ("revision", SemanticAtom
      (unNextStageRequirementRevision
        (nextStageRequirementRevision requirement)))
  , ("body", semanticRequirementBody requirement)
  ])

semanticRequirementBody :: NextStageRequirement -> SemanticForm
semanticRequirementBody requirement = SemanticRecord (Map.fromList
  [ ("basis", semanticBasis (nextStageRequirementBasis requirement))
  , ("source_refs", SemanticUnordered
      (Set.map semanticSourceRef
        (nextStageRequirementSourceSystemsRefs requirement)))
  , ("required_fact", SemanticAtom
      (nextStageRequirementRequiredFactOrContract requirement))
  , ("acceptance_rule", SemanticAtom
      (nextStageRequirementAcceptanceRule requirement))
  , ("validity_scope", SemanticAtom
      (unNextStageValidityScope
        (nextStageRequirementValidityScope requirement)))
  ])

semanticBasis :: NextStageRequirementBasis -> SemanticForm
semanticBasis basis = case basis of
  NextStageTargetPreconditionBasis ref -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "target-precondition")
    , ("decision", SemanticAtom
        (unDecisionId (targetPreconditionDecision ref)))
    , ("requirement", SemanticAtom
        (targetPreconditionRequirement ref))
    ])
  NextStageRuntimePrimitiveBasis profile -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "runtime-primitive")
    , ("profile", SemanticAtom
        (unRuntimePrimitiveProfileRef profile))
    ])

semanticSourceRef :: NextStageSourceRef -> SemanticForm
semanticSourceRef sourceRef = case sourceRef of
  NextStageTargetPreconditionSource ref -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "target-precondition")
    , ("decision", SemanticAtom
        (unDecisionId (targetPreconditionDecision ref)))
    , ("requirement", SemanticAtom
        (targetPreconditionRequirement ref))
    ])
  NextStageRuntimePrimitiveSource profile -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "runtime-primitive")
    , ("profile", SemanticAtom
        (unRuntimePrimitiveProfileRef profile))
    ])
  NextStageRuntimeSiteSource site -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "runtime-site")
    , ("function", SemanticAtom (runtimeSiteFunction site))
    , ("block", SemanticAtom (unBlockId (runtimeSiteBlock site)))
    , ("slot", SemanticAtom (renderSiteSlot (runtimeSiteSlot site)))
    ])
  NextStageSemanticSubjectSource subject -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "semantic-subject")
    , ("subject", SemanticAtom subject)
    ])
  NextStageSourceAssurance revision -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "source-assurance")
    , ("revision", SemanticAtom (unRevisionId revision))
    ])
  NextStageDerivedObligationSource revision -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "derived-obligation")
    , ("revision", SemanticAtom (unRevisionId revision))
    ])
  NextStageCostChargeSource charge -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "cost-charge")
    , ("charge", SemanticAtom (unCostChargeIdentity charge))
    ])

renderSiteSlot :: RuntimeSiteSlot -> Text
renderSiteSlot slot = case slot of
  RuntimeOperationSite index -> "op:" <> Text.pack (show index)
  RuntimeTerminatorSite -> "terminator"

duplicateKeys :: Ord a => [a] -> Set a
duplicateKeys values = Map.keysSet (Map.filter (> (1 :: Int)) counts)
  where
    counts = Map.fromListWith (+)
      [ (value, 1 :: Int)
      | value <- values
      ]

requireEqual
  :: Eq a
  => (a -> a -> NextStageRequirementVerificationError)
  -> a
  -> a
  -> Either NextStageRequirementVerificationError ()
requireEqual constructor expected actual
  | expected == actual = Right ()
  | otherwise = Left (constructor expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
