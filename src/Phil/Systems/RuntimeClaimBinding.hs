{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RuntimeClaimBinding
  ( RuntimeClaimStageRevision (..)
  , RuntimeSiteSlot (..)
  , RuntimeSiteKey (..)
  , PhysicalRuntimeCostIdentity (..)
  , RuntimeSiteBinding (..)
  , RuntimeClaimRevision (..)
  , RuntimeClaim (..)
  , RuntimeClaimBinding (..)
  , PhysicalRuntimeCost (..)
  , RuntimeClaimStageBundle (..)
  , RuntimeClaimVerificationError (..)
  , deriveRuntimeSiteBindings
  , deriveRuntimeClaimSourceFacts
  , derivePhysicalRuntimeCosts
  , deriveRuntimeClaimReverse
  , deriveRuntimeClaimStageRevision
  , makeRuntimeClaimStageBundle
  , completeRuntimeClaimStageBundle
  , verifyRuntimeClaimStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( EvidenceEntryId (..)
  , RevisionId (..)
  )
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.AssumptionDependency
  ( AssumptionDependencyStageBundle (..)
  )
import Phil.Systems.EvidenceErasure
  ( EvidenceErasureStageBundle (..)
  )
import Phil.Systems.EvidenceSubjectTransfer
  ( EvidenceTransferStageBundle (..)
  )
import Phil.Systems.IR
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  , SourceFactKey (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )
import Phil.Systems.TargetStrengthening
  ( TargetStrengtheningStageBundle (..)
  , TargetStrengtheningStageRevision (..)
  , TargetStrengtheningVerificationError
  , verifyTargetStrengtheningStageBundle
  )

newtype RuntimeClaimStageRevision = RuntimeClaimStageRevision
  { unRuntimeClaimStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

data RuntimeSiteSlot
  = RuntimeOperationSite Int
  | RuntimeTerminatorSite
  deriving (Eq, Ord, Show)

data RuntimeSiteKey = RuntimeSiteKey
  { runtimeSiteFunction :: Text
  , runtimeSiteBlock :: BlockId
  , runtimeSiteSlot :: RuntimeSiteSlot
  }
  deriving (Eq, Ord, Show)

newtype PhysicalRuntimeCostIdentity = PhysicalRuntimeCostIdentity
  { unPhysicalRuntimeCostIdentity :: Text
  }
  deriving (Eq, Ord, Show)

data RuntimeSiteBinding = RuntimeSiteBinding
  { runtimeSiteBindingKey :: RuntimeSiteKey
  , runtimeSiteBindingRef :: RuntimeSiteRef
  , runtimeSiteBindingCostIdentity :: PhysicalRuntimeCostIdentity
  }
  deriving (Eq, Ord, Show)

newtype RuntimeClaimRevision = RuntimeClaimRevision
  { unRuntimeClaimRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | A runtime assurance claim may summarize one or several exact source
-- obligations.  SYS-015 checks only the claim/site accounting relation; later
-- assurance/carrier slices decide whether the claim is adequately enforced.
data RuntimeClaim = RuntimeClaim
  { runtimeClaimRevision :: RuntimeClaimRevision
  , runtimeClaimSourceObligations :: Set RevisionId
  , runtimeClaimSourceFacts :: Set SourceFactKey
  , runtimeClaimSemanticSubjects :: Set Text
  }
  deriving (Eq, Ord, Show)

-- | Claims refer to physical cost identities, but they do not own or duplicate
-- those costs.  The cost registry below is site-indexed exactly once.
data RuntimeClaimBinding = RuntimeClaimBinding
  { runtimeClaimBindingRevision :: RuntimeClaimRevision
  , runtimeClaimBindingSites :: Set RuntimeSiteKey
  , runtimeClaimBindingCostIdentities :: Set PhysicalRuntimeCostIdentity
  }
  deriving (Eq, Ord, Show)

data PhysicalRuntimeCost = PhysicalRuntimeCost
  { physicalRuntimeCostIdentity :: PhysicalRuntimeCostIdentity
  , physicalRuntimeCostSite :: RuntimeSiteKey
  , physicalRuntimeCostRef :: Text
  }
  deriving (Eq, Ord, Show)

data RuntimeClaimStageBundle = RuntimeClaimStageBundle
  { runtimeClaimStageBase :: TargetStrengtheningStageBundle
  , runtimeClaimStageRevision :: RuntimeClaimStageRevision
  , runtimeClaimStageSites :: Map RuntimeSiteKey RuntimeSiteBinding
  , runtimeClaimStageClaims :: Map RuntimeClaimRevision RuntimeClaim
  , runtimeClaimStageBindings :: Map RuntimeClaimRevision RuntimeClaimBinding
  , runtimeClaimStageReverse :: Map RuntimeSiteKey (Set RuntimeClaimRevision)
  , runtimeClaimStagePhysicalCosts
      :: Map PhysicalRuntimeCostIdentity PhysicalRuntimeCost
  }
  deriving (Eq, Show)

data RuntimeClaimVerificationError
  = RuntimeClaimBaseError TargetStrengtheningVerificationError
  | RuntimeClaimStageRevisionMismatch
      RuntimeClaimStageRevision RuntimeClaimStageRevision
  | RuntimeSiteDomainMismatch
      (Set RuntimeSiteKey) (Set RuntimeSiteKey)
  | RuntimeSiteBindingMismatch
      RuntimeSiteKey RuntimeSiteBinding RuntimeSiteBinding
  | RuntimeSiteEmptyCostRef RuntimeSiteKey
  | RuntimeClaimDomainMismatch
      (Set RuntimeClaimRevision) (Set RuntimeClaimRevision)
  | RuntimeClaimMapKeyMismatch
      RuntimeClaimRevision RuntimeClaimRevision
  | RuntimeClaimBindingMapKeyMismatch
      RuntimeClaimRevision RuntimeClaimRevision
  | RuntimeClaimEmptyRevision
  | RuntimeClaimEmptySourceObligations RuntimeClaimRevision
  | RuntimeClaimEmptySiteSet RuntimeClaimRevision
  | RuntimeClaimUnknownSites RuntimeClaimRevision (Set RuntimeSiteKey)
  | RuntimeClaimObligationSiteMismatch
      RuntimeClaimRevision (Set RevisionId) (Set RevisionId)
  | RuntimeClaimUnknownSourceObligations
      RuntimeClaimRevision (Set RevisionId)
  | RuntimeClaimSourceFactMismatch
      RuntimeClaimRevision (Set SourceFactKey) (Set SourceFactKey)
  | RuntimeClaimCostIdentityMismatch
      RuntimeClaimRevision
      (Set PhysicalRuntimeCostIdentity)
      (Set PhysicalRuntimeCostIdentity)
  | RuntimeSiteUnclaimed RuntimeSiteKey
  | RuntimeClaimReverseDomainMismatch
      (Set RuntimeSiteKey) (Set RuntimeSiteKey)
  | RuntimeClaimReverseClaimsMismatch
      RuntimeSiteKey (Set RuntimeClaimRevision) (Set RuntimeClaimRevision)
  | RuntimeCostRegistryDomainMismatch
      (Set PhysicalRuntimeCostIdentity)
      (Set PhysicalRuntimeCostIdentity)
  | RuntimeCostBindingMismatch
      PhysicalRuntimeCostIdentity PhysicalRuntimeCost PhysicalRuntimeCost
  deriving (Eq, Show)

deriveRuntimeSiteBindings
  :: TargetStrengtheningStageBundle
  -> Map RuntimeSiteKey RuntimeSiteBinding
deriveRuntimeSiteBindings base = Map.fromList
  (concatMap functionSites (Map.toAscList functions))
  where
    functions = systemsProgramFunctions
      (systemsArtifactProgram (baseArtifact base))

    functionSites (functionKey, function) = concatMap
      (blockSites functionKey)
      (Map.toAscList (systemsFunctionBlocks function))

    blockSites functionKey (blockKey, blockValue) =
      operationSites functionKey blockKey (systemsBlockOps blockValue)
      <> terminatorSites functionKey blockKey
          (systemsBlockTerminator blockValue)

    operationSites functionKey blockKey operations =
      [ pairSite key site
      | (index, operation) <- zip [(0 :: Int) ..] operations
      , Just site <- [operationRuntimeSite operation]
      , let key = RuntimeSiteKey
              functionKey blockKey (RuntimeOperationSite index)
      ]

    terminatorSites functionKey blockKey terminator = case terminatorRuntimeSite terminator of
      Nothing -> []
      Just site ->
        [pairSite (RuntimeSiteKey functionKey blockKey RuntimeTerminatorSite) site]

pairSite :: RuntimeSiteKey -> RuntimeSiteRef -> (RuntimeSiteKey, RuntimeSiteBinding)
pairSite key site = (key, RuntimeSiteBinding
  { runtimeSiteBindingKey = key
  , runtimeSiteBindingRef = site
  , runtimeSiteBindingCostIdentity = physicalCostIdentityFor key site
  })

operationRuntimeSite :: SystemsOp -> Maybe RuntimeSiteRef
operationRuntimeSite operation = case operation of
  OpRuntimeCall { runtimeCallSite = site } -> site
  _ -> Nothing

terminatorRuntimeSite :: SystemsTerminator -> Maybe RuntimeSiteRef
terminatorRuntimeSite terminator = case terminator of
  TermRecognize { recognizeSite = site } -> Just site
  TermRuntimeCheck { checkSite = site } -> Just site
  TermReceiveExact { exactSite = site } -> Just site
  TermSendExact { sendExactSite = site } -> Just site
  TermStore { storeSite = site } -> Just site
  TermRuntimeChoice { runtimeChoiceSite = site } -> site
  _ -> Nothing

physicalCostIdentityFor
  :: RuntimeSiteKey
  -> RuntimeSiteRef
  -> PhysicalRuntimeCostIdentity
physicalCostIdentityFor key site = PhysicalRuntimeCostIdentity
  ("phil.phase1.runtime-cost.site:"
    <> renderRuntimeSiteKey key
    <> ":"
    <> runtimeSiteCostRef site)

deriveRuntimeClaimSourceFacts
  :: TargetStrengtheningStageBundle
  -> Set RevisionId
  -> Set SourceFactKey
deriveRuntimeClaimSourceFacts base revisions = Set.fromList
  [ SourceFactKey (factTransferId fact)
  | fact <- stageFacts (systemsArtifactStageContract (baseArtifact base))
  , Just revision <- [factSourceRevision fact]
  , Set.member revision revisions
  ]

deriveSourceObligationRevisions
  :: TargetStrengtheningStageBundle
  -> Set RevisionId
deriveSourceObligationRevisions base = Set.fromList
  [ revision
  | fact <- stageFacts (systemsArtifactStageContract (baseArtifact base))
  , Just revision <- [factSourceRevision fact]
  ]

derivePhysicalRuntimeCosts
  :: Map RuntimeSiteKey RuntimeSiteBinding
  -> Map PhysicalRuntimeCostIdentity PhysicalRuntimeCost
derivePhysicalRuntimeCosts sites = Map.fromList
  [ (costIdentity, PhysicalRuntimeCost
      { physicalRuntimeCostIdentity = costIdentity
      , physicalRuntimeCostSite = siteKey
      , physicalRuntimeCostRef = runtimeSiteCostRef (runtimeSiteBindingRef binding)
      })
  | (siteKey, binding) <- Map.toAscList sites
  , let costIdentity = runtimeSiteBindingCostIdentity binding
  ]

deriveRuntimeClaimReverse
  :: Map RuntimeClaimRevision RuntimeClaimBinding
  -> Map RuntimeSiteKey (Set RuntimeClaimRevision)
deriveRuntimeClaimReverse bindings = Map.fromListWith Set.union
  [ (site, Set.singleton claimRevision)
  | (claimRevision, binding) <- Map.toAscList bindings
  , site <- Set.toAscList (runtimeClaimBindingSites binding)
  ]

deriveRuntimeClaimStageRevision
  :: RuntimeClaimStageBundle
  -> RuntimeClaimStageRevision
deriveRuntimeClaimStageRevision bundle = RuntimeClaimStageRevision
  ("phil.phase1.stage.runtime-claims.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom
          (unTargetStrengtheningStageRevision
            (targetStrengtheningStageRevision (runtimeClaimStageBase bundle))))
      , ("sites", SemanticUnordered (Set.fromList
          [ semanticSiteBinding binding
          | (_, binding) <- Map.toAscList (runtimeClaimStageSites bundle)
          ]))
      , ("claims", SemanticUnordered (Set.fromList
          [ semanticClaim claim
          | (_, claim) <- Map.toAscList (runtimeClaimStageClaims bundle)
          ]))
      , ("bindings", SemanticUnordered (Set.fromList
          [ semanticClaimBinding binding
          | (_, binding) <- Map.toAscList (runtimeClaimStageBindings bundle)
          ]))
      , ("reverse", SemanticUnordered (Set.fromList
          [ SemanticRecord (Map.fromList
              [ ("site", semanticSiteKey site)
              , ("claims", semanticClaimRevisionSet claims)
              ])
          | (site, claims) <- Map.toAscList (runtimeClaimStageReverse bundle)
          ]))
      , ("physical_costs", SemanticUnordered (Set.fromList
          [ semanticPhysicalCost cost
          | (_, cost) <- Map.toAscList (runtimeClaimStagePhysicalCosts bundle)
          ]))
      ])))

makeRuntimeClaimStageBundle
  :: TargetStrengtheningStageBundle
  -> Map RuntimeSiteKey RuntimeSiteBinding
  -> Map RuntimeClaimRevision RuntimeClaim
  -> Map RuntimeClaimRevision RuntimeClaimBinding
  -> Map RuntimeSiteKey (Set RuntimeClaimRevision)
  -> Map PhysicalRuntimeCostIdentity PhysicalRuntimeCost
  -> RuntimeClaimStageBundle
makeRuntimeClaimStageBundle base sites claims bindings reverse costs = provisional
  { runtimeClaimStageRevision = deriveRuntimeClaimStageRevision provisional }
  where
    provisional = RuntimeClaimStageBundle
      { runtimeClaimStageBase = base
      , runtimeClaimStageRevision = RuntimeClaimStageRevision "pending"
      , runtimeClaimStageSites = sites
      , runtimeClaimStageClaims = claims
      , runtimeClaimStageBindings = bindings
      , runtimeClaimStageReverse = reverse
      , runtimeClaimStagePhysicalCosts = costs
      }

completeRuntimeClaimStageBundle
  :: TargetStrengtheningStageBundle
  -> Map RuntimeClaimRevision RuntimeClaim
  -> Map RuntimeClaimRevision RuntimeClaimBinding
  -> RuntimeClaimStageBundle
completeRuntimeClaimStageBundle base claims bindings =
  makeRuntimeClaimStageBundle base sites claims bindings reverse costs
  where
    sites = deriveRuntimeSiteBindings base
    reverse = deriveRuntimeClaimReverse bindings
    costs = derivePhysicalRuntimeCosts sites

verifyRuntimeClaimStageBundle
  :: RuntimeClaimStageBundle
  -> Either RuntimeClaimVerificationError ()
verifyRuntimeClaimStageBundle bundle = do
  mapLeft RuntimeClaimBaseError $
    verifyTargetStrengtheningStageBundle (runtimeClaimStageBase bundle)
  requireEqual RuntimeClaimStageRevisionMismatch
    (deriveRuntimeClaimStageRevision bundle)
    (runtimeClaimStageRevision bundle)

  let expectedSites = deriveRuntimeSiteBindings (runtimeClaimStageBase bundle)
      actualSites = runtimeClaimStageSites bundle
  requireEqual RuntimeSiteDomainMismatch
    (Map.keysSet expectedSites) (Map.keysSet actualSites)
  mapM_ (checkSiteBinding actualSites) (Map.toAscList expectedSites)

  let claims = runtimeClaimStageClaims bundle
      bindings = runtimeClaimStageBindings bundle
  requireEqual RuntimeClaimDomainMismatch
    (Map.keysSet claims) (Map.keysSet bindings)
  mapM_ (checkClaim bundle) (Map.toAscList claims)

  let expectedReverse = deriveRuntimeClaimReverse bindings
  mapM_ (requireClaimed expectedReverse) (Map.keys expectedSites)
  requireEqual RuntimeClaimReverseDomainMismatch
    (Map.keysSet expectedSites) (Map.keysSet (runtimeClaimStageReverse bundle))
  mapM_ (checkReverse bundle expectedReverse) (Map.keys expectedSites)

  let expectedCosts = derivePhysicalRuntimeCosts expectedSites
      actualCosts = runtimeClaimStagePhysicalCosts bundle
  requireEqual RuntimeCostRegistryDomainMismatch
    (Map.keysSet expectedCosts) (Map.keysSet actualCosts)
  mapM_ (checkCost actualCosts) (Map.toAscList expectedCosts)

checkSiteBinding
  :: Map RuntimeSiteKey RuntimeSiteBinding
  -> (RuntimeSiteKey, RuntimeSiteBinding)
  -> Either RuntimeClaimVerificationError ()
checkSiteBinding actualSites (key, expected) = case Map.lookup key actualSites of
  Nothing -> Left (RuntimeSiteDomainMismatch (Set.singleton key) Set.empty)
  Just actual -> do
    requireEqual (RuntimeSiteBindingMismatch key) expected actual
    if Text.null (runtimeSiteCostRef (runtimeSiteBindingRef actual))
      then Left (RuntimeSiteEmptyCostRef key)
      else Right ()

checkClaim
  :: RuntimeClaimStageBundle
  -> (RuntimeClaimRevision, RuntimeClaim)
  -> Either RuntimeClaimVerificationError ()
checkClaim bundle (key, claim) = do
  requireEqual RuntimeClaimMapKeyMismatch key (runtimeClaimRevision claim)
  if Text.null (unRuntimeClaimRevision key)
    then Left RuntimeClaimEmptyRevision
    else Right ()
  if Set.null (runtimeClaimSourceObligations claim)
    then Left (RuntimeClaimEmptySourceObligations key)
    else Right ()

  binding <- case Map.lookup key (runtimeClaimStageBindings bundle) of
    Nothing -> Left (RuntimeClaimDomainMismatch
      (Map.keysSet (runtimeClaimStageClaims bundle))
      (Map.keysSet (runtimeClaimStageBindings bundle)))
    Just value -> Right value
  requireEqual RuntimeClaimBindingMapKeyMismatch
    key (runtimeClaimBindingRevision binding)
  if Set.null (runtimeClaimBindingSites binding)
    then Left (RuntimeClaimEmptySiteSet key)
    else Right ()

  let sites = runtimeClaimStageSites bundle
      unknownSites = Set.difference
        (runtimeClaimBindingSites binding) (Map.keysSet sites)
  if Set.null unknownSites
    then Right ()
    else Left (RuntimeClaimUnknownSites key unknownSites)

  let siteObligations = Set.fromList
        [ runtimeSiteRevision (runtimeSiteBindingRef siteBinding)
        | site <- Set.toAscList (runtimeClaimBindingSites binding)
        , Just siteBinding <- [Map.lookup site sites]
        ]
  requireEqual (RuntimeClaimObligationSiteMismatch key)
    siteObligations (runtimeClaimSourceObligations claim)

  let knownSourceObligations = deriveSourceObligationRevisions
        (runtimeClaimStageBase bundle)
      unknownObligations = Set.difference
        (runtimeClaimSourceObligations claim) knownSourceObligations
  if Set.null unknownObligations
    then Right ()
    else Left (RuntimeClaimUnknownSourceObligations key unknownObligations)

  let expectedFacts = deriveRuntimeClaimSourceFacts
        (runtimeClaimStageBase bundle)
        (runtimeClaimSourceObligations claim)
  requireEqual (RuntimeClaimSourceFactMismatch key)
    expectedFacts (runtimeClaimSourceFacts claim)

  let expectedCostIdentities = Set.fromList
        [ runtimeSiteBindingCostIdentity siteBinding
        | site <- Set.toAscList (runtimeClaimBindingSites binding)
        , Just siteBinding <- [Map.lookup site sites]
        ]
  requireEqual (RuntimeClaimCostIdentityMismatch key)
    expectedCostIdentities (runtimeClaimBindingCostIdentities binding)

requireClaimed
  :: Map RuntimeSiteKey (Set RuntimeClaimRevision)
  -> RuntimeSiteKey
  -> Either RuntimeClaimVerificationError ()
requireClaimed expectedReverse site = case Map.lookup site expectedReverse of
  Just claims | not (Set.null claims) -> Right ()
  _ -> Left (RuntimeSiteUnclaimed site)

checkReverse
  :: RuntimeClaimStageBundle
  -> Map RuntimeSiteKey (Set RuntimeClaimRevision)
  -> RuntimeSiteKey
  -> Either RuntimeClaimVerificationError ()
checkReverse bundle expectedReverse site = do
  let expected = Map.findWithDefault Set.empty site expectedReverse
      actual = Map.findWithDefault Set.empty site
        (runtimeClaimStageReverse bundle)
  requireEqual (RuntimeClaimReverseClaimsMismatch site) expected actual

checkCost
  :: Map PhysicalRuntimeCostIdentity PhysicalRuntimeCost
  -> (PhysicalRuntimeCostIdentity, PhysicalRuntimeCost)
  -> Either RuntimeClaimVerificationError ()
checkCost actualCosts (key, expected) = case Map.lookup key actualCosts of
  Nothing -> Left (RuntimeCostRegistryDomainMismatch
    (Set.singleton key) Set.empty)
  Just actual -> requireEqual (RuntimeCostBindingMismatch key) expected actual

baseArtifact :: TargetStrengtheningStageBundle -> SystemsArtifact
baseArtifact =
  phase1StageSystemsArtifact
    . subjectStageBase
    . evidenceTransferStageBase
    . evidenceErasureStageBase
    . assumptionDependencyStageBase
    . targetStrengtheningStageBase

renderRuntimeSiteKey :: RuntimeSiteKey -> Text
renderRuntimeSiteKey key = Text.intercalate ":"
  [ runtimeSiteFunction key
  , unBlockId (runtimeSiteBlock key)
  , renderRuntimeSiteSlot (runtimeSiteSlot key)
  ]

renderRuntimeSiteSlot :: RuntimeSiteSlot -> Text
renderRuntimeSiteSlot slot = case slot of
  RuntimeOperationSite index -> "op." <> Text.pack (show index)
  RuntimeTerminatorSite -> "term"

renderRuntimeSiteKind :: RuntimeSiteKind -> Text
renderRuntimeSiteKind kind = case kind of
  RecognitionBoundary name -> "recognition:" <> name
  ValidationBoundary name -> "validation:" <> name
  BranchRefinementBoundary name -> "branch-refinement:" <> name
  ExactReceiveBoundary -> "exact-receive"
  ExactSendBoundary -> "exact-send"
  DigestBoundary -> "digest"
  StorageBoundary -> "storage"
  SourceSemanticRuntime name -> "source-runtime:" <> name

semanticSiteKey :: RuntimeSiteKey -> SemanticForm
semanticSiteKey key = SemanticRecord (Map.fromList
  [ ("function", SemanticAtom (runtimeSiteFunction key))
  , ("block", SemanticAtom (unBlockId (runtimeSiteBlock key)))
  , ("slot", SemanticAtom (renderRuntimeSiteSlot (runtimeSiteSlot key)))
  ])

semanticSiteBinding :: RuntimeSiteBinding -> SemanticForm
semanticSiteBinding binding = SemanticRecord (Map.fromList
  [ ("key", semanticSiteKey (runtimeSiteBindingKey binding))
  , ("kind", SemanticAtom
      (renderRuntimeSiteKind (runtimeSiteKind (runtimeSiteBindingRef binding))))
  , ("obligation", SemanticAtom
      (unRevisionId (runtimeSiteRevision (runtimeSiteBindingRef binding))))
  , ("evidence", SemanticAtom
      (unEvidenceEntryId (runtimeSiteEvidence (runtimeSiteBindingRef binding))))
  , ("cost_ref", SemanticAtom
      (runtimeSiteCostRef (runtimeSiteBindingRef binding)))
  , ("physical_cost", SemanticAtom
      (unPhysicalRuntimeCostIdentity
        (runtimeSiteBindingCostIdentity binding)))
  ])

semanticClaim :: RuntimeClaim -> SemanticForm
semanticClaim claim = SemanticRecord (Map.fromList
  [ ("revision", SemanticAtom
      (unRuntimeClaimRevision (runtimeClaimRevision claim)))
  , ("source_obligations", semanticRevisionSet
      (runtimeClaimSourceObligations claim))
  , ("source_facts", SemanticUnordered
      (Set.map (SemanticAtom . unSourceFactKey)
        (runtimeClaimSourceFacts claim)))
  , ("subjects", semanticTextSet (runtimeClaimSemanticSubjects claim))
  ])

semanticClaimBinding :: RuntimeClaimBinding -> SemanticForm
semanticClaimBinding binding = SemanticRecord (Map.fromList
  [ ("claim", SemanticAtom
      (unRuntimeClaimRevision (runtimeClaimBindingRevision binding)))
  , ("sites", SemanticUnordered
      (Set.map semanticSiteKey (runtimeClaimBindingSites binding)))
  , ("cost_identities", SemanticUnordered
      (Set.map (SemanticAtom . unPhysicalRuntimeCostIdentity)
        (runtimeClaimBindingCostIdentities binding)))
  ])

semanticPhysicalCost :: PhysicalRuntimeCost -> SemanticForm
semanticPhysicalCost cost = SemanticRecord (Map.fromList
  [ ("identity", SemanticAtom
      (unPhysicalRuntimeCostIdentity (physicalRuntimeCostIdentity cost)))
  , ("site", semanticSiteKey (physicalRuntimeCostSite cost))
  , ("cost_ref", SemanticAtom (physicalRuntimeCostRef cost))
  ])

semanticClaimRevisionSet :: Set RuntimeClaimRevision -> SemanticForm
semanticClaimRevisionSet = SemanticUnordered
  . Set.map (SemanticAtom . unRuntimeClaimRevision)

semanticRevisionSet :: Set RevisionId -> SemanticForm
semanticRevisionSet = SemanticUnordered . Set.map (SemanticAtom . unRevisionId)

semanticTextSet :: Set Text -> SemanticForm
semanticTextSet = SemanticUnordered . Set.map SemanticAtom

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
