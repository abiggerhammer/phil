{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.CostAttribution
  ( CostAttributionStageRevision (..)
  , CostChargeIdentity (..)
  , CostContributionIdentity (..)
  , RuntimeCostBasis (..)
  , CostMechanism (..)
  , CostContribution (..)
  , AttributedCost (..)
  , CostAttributionStageBundle (..)
  , CostAttributionVerificationError (..)
  , deriveExpectedCostContributions
  , deriveContributionCharges
  , deriveAttributedCosts
  , deriveRuntimeSiteContributions
  , deriveClaimCharges
  , deriveStagingContributions
  , deriveCostAttributionStageRevision
  , makeCostAttributionStageBundle
  , completeCostAttributionStageBundle
  , verifyCostAttributionStageBundle
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
  ( BlockId (..)
  , CostClass (..)
  , CostShape (..)
  , DecisionId (..)
  , LoweringDecision (..)
  , LoweringLedger (..)
  , SystemsArtifact (..)
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import Phil.Systems.RuntimeClaimBinding
  ( PhysicalRuntimeCostIdentity (..)
  , RuntimeClaimRevision (..)
  , RuntimeClaimStageBundle (..)
  , RuntimeSiteKey (..)
  , RuntimeSiteSlot (..)
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  , RuntimePrimitiveSiteBinding (..)
  , RuntimePrimitiveStageBundle (..)
  )
import Phil.Systems.StagingEffect
  ( StagingCostAccount (..)
  , StagingCostIdentity (..)
  , StagingEffectStageBundle (..)
  , StagingEffectStageRevision (..)
  , StagingEffectVerificationError
  , StagingEvent (..)
  , StagingRequirementKey (..)
  , verifyStagingEffectStageBundle
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )
import Phil.Systems.TargetStrengthening
  ( TargetStrengtheningStageBundle (..)
  )

newtype CostAttributionStageRevision = CostAttributionStageRevision
  { unCostAttributionStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Final physical/accounting line-item identity. Several site-owned
-- contributions may map to one charge when the selected cost profile says they
-- are one shared mechanism with one cost shape/frequency expression.
newtype CostChargeIdentity = CostChargeIdentity
  { unCostChargeIdentity :: Text
  }
  deriving (Eq, Ord, Show)

-- | Predecessor identities remain visible as contributions. SYS-015's
-- PhysicalRuntimeCostIdentity is site-owned; SYS-017's StagingCostIdentity is
-- event-owned. SYS-018 may aggregate contributions without erasing either.
data CostContributionIdentity
  = RuntimeCostContribution PhysicalRuntimeCostIdentity
  | StagingCostContribution StagingCostIdentity
  deriving (Eq, Ord, Show)

-- | Selected profile relation from one reusable runtime primitive/profile to
-- the exact ADR-011 lowering decision that supplies class/shape and the final
-- physical charge to which occurrences of that mechanism contribute.
data RuntimeCostBasis = RuntimeCostBasis
  { runtimeCostBasisProfile :: RuntimePrimitiveProfileRef
  , runtimeCostBasisDecision :: DecisionId
  , runtimeCostBasisCharge :: CostChargeIdentity
  }
  deriving (Eq, Ord, Show)

data CostMechanism
  = RuntimeSiteCostMechanism RuntimeSiteKey RuntimePrimitiveProfileRef DecisionId
  | StagingCostMechanism StagingRequirementKey
  deriving (Eq, Ord, Show)

data CostContribution = CostContribution
  { costContributionIdentity :: CostContributionIdentity
  , costContributionMechanism :: CostMechanism
  , costContributionClass :: CostClass
  , costContributionShape :: CostShape
  , costContributionRuntimeClaims :: Set RuntimeClaimRevision
  }
  deriving (Eq, Ord, Show)

-- | Claims never own charge entries. Multiple contributions may share a charge
-- only when class and shape agree exactly; the charge retains every contributing
-- identity and the union of exact runtime claims.
data AttributedCost = AttributedCost
  { attributedCostIdentity :: CostChargeIdentity
  , attributedCostClass :: CostClass
  , attributedCostShape :: CostShape
  , attributedCostContributions :: Set CostContributionIdentity
  , attributedCostRuntimeClaims :: Set RuntimeClaimRevision
  }
  deriving (Eq, Ord, Show)

data CostAttributionStageBundle = CostAttributionStageBundle
  { costAttributionStageBase :: StagingEffectStageBundle
  , costAttributionStageRevision :: CostAttributionStageRevision
  , costAttributionStageRuntimeBases
      :: Map RuntimePrimitiveProfileRef RuntimeCostBasis
  , costAttributionStageContributions
      :: Map CostContributionIdentity CostContribution
  , costAttributionStageContributionCharges
      :: Map CostContributionIdentity CostChargeIdentity
  , costAttributionStageCharges
      :: Map CostChargeIdentity AttributedCost
  , costAttributionStageRuntimeSiteContributions
      :: Map RuntimeSiteKey CostContributionIdentity
  , costAttributionStageClaimCharges
      :: Map RuntimeClaimRevision (Set CostChargeIdentity)
  , costAttributionStageStagingContributions
      :: Map StagingRequirementKey CostContributionIdentity
  }
  deriving (Eq, Show)

data CostAttributionVerificationError
  = CostAttributionBaseError StagingEffectVerificationError
  | CostAttributionStageRevisionMismatch
      CostAttributionStageRevision CostAttributionStageRevision
  | RuntimeCostBasisDomainMismatch
      (Set RuntimePrimitiveProfileRef)
      (Set RuntimePrimitiveProfileRef)
  | RuntimeCostBasisMapKeyMismatch
      RuntimePrimitiveProfileRef RuntimePrimitiveProfileRef
  | RuntimeCostBasisUnknownDecision
      RuntimePrimitiveProfileRef DecisionId
  | RuntimeCostBasisMissingClass
      RuntimePrimitiveProfileRef DecisionId
  | RuntimeCostBasisEmptyShape
      RuntimePrimitiveProfileRef DecisionId
  | RuntimeCostBasisEmptyCharge RuntimePrimitiveProfileRef
  | CostContributionIdentityCollision
      (Set CostContributionIdentity)
  | CostContributionDomainMismatch
      (Set CostContributionIdentity)
      (Set CostContributionIdentity)
  | CostContributionMapKeyMismatch
      CostContributionIdentity CostContributionIdentity
  | CostContributionEntryMismatch
      CostContributionIdentity CostContribution CostContribution
  | ContributionChargeMismatch
      (Map CostContributionIdentity CostChargeIdentity)
      (Map CostContributionIdentity CostChargeIdentity)
  | CostChargeIncompatibleClass
      CostChargeIdentity (Set CostClass)
  | CostChargeIncompatibleShape
      CostChargeIdentity (Set CostShape)
  | CostChargeEmptyContributionSet CostChargeIdentity
  | AttributedCostDomainMismatch
      (Set CostChargeIdentity)
      (Set CostChargeIdentity)
  | AttributedCostMapKeyMismatch
      CostChargeIdentity CostChargeIdentity
  | AttributedCostEntryMismatch
      CostChargeIdentity AttributedCost AttributedCost
  | RuntimeSiteContributionMismatch
      (Map RuntimeSiteKey CostContributionIdentity)
      (Map RuntimeSiteKey CostContributionIdentity)
  | RuntimeClaimChargeMismatch
      (Map RuntimeClaimRevision (Set CostChargeIdentity))
      (Map RuntimeClaimRevision (Set CostChargeIdentity))
  | StagingContributionMismatch
      (Map StagingRequirementKey CostContributionIdentity)
      (Map StagingRequirementKey CostContributionIdentity)
  deriving (Eq, Show)

deriveExpectedCostContributions
  :: StagingEffectStageBundle
  -> Map RuntimePrimitiveProfileRef RuntimeCostBasis
  -> Either CostAttributionVerificationError
       (Map CostContributionIdentity CostContribution)
deriveExpectedCostContributions base bases = do
  validateRuntimeBases base bases
  runtime <- mapM (runtimeContribution base bases)
    (Map.toAscList (runtimePrimitiveStageSites
      (stagingEffectStageBase base)))
  staging <- mapM stagingContribution
    (Map.toAscList (stagingEffectStageEvents base))
  let pairs = runtime <> staging
      result = Map.fromList pairs
  if Map.size result == length pairs
    then Right result
    else Left (CostContributionIdentityCollision
      (duplicateKeys (map fst pairs)))

deriveContributionCharges
  :: Map RuntimePrimitiveProfileRef RuntimeCostBasis
  -> Map CostContributionIdentity CostContribution
  -> Map CostContributionIdentity CostChargeIdentity
deriveContributionCharges bases contributions = Map.fromList
  [ (identity, chargeFor contribution)
  | (identity, contribution) <- Map.toAscList contributions
  ]
  where
    chargeFor contribution = case costContributionMechanism contribution of
      RuntimeSiteCostMechanism _ profile _ ->
        case Map.lookup profile bases of
          Just basis -> runtimeCostBasisCharge basis
          Nothing -> CostChargeIdentity "missing-runtime-cost-basis"
      StagingCostMechanism _ -> case costContributionIdentity contribution of
        StagingCostContribution stagingIdentity ->
          CostChargeIdentity
            ("staging:" <> unStagingCostIdentity stagingIdentity)
        RuntimeCostContribution _ ->
          CostChargeIdentity "invalid-staging-contribution"

deriveAttributedCosts
  :: Map CostContributionIdentity CostContribution
  -> Map CostContributionIdentity CostChargeIdentity
  -> Either CostAttributionVerificationError
       (Map CostChargeIdentity AttributedCost)
deriveAttributedCosts contributions contributionCharges =
  Map.traverseWithKey buildCharge grouped
  where
    grouped = Map.fromListWith Set.union
      [ (charge, Set.singleton contributionIdentity)
      | (contributionIdentity, charge) <-
          Map.toAscList contributionCharges
      ]

    buildCharge charge contributionIds
      | Set.null contributionIds =
          Left (CostChargeEmptyContributionSet charge)
      | otherwise = do
          entries <- mapM lookupContribution
            (Set.toAscList contributionIds)
          let classes = Set.fromList
                (map costContributionClass entries)
              shapes = Set.fromList
                (map costContributionShape entries)
              claims = Set.unions
                (map costContributionRuntimeClaims entries)
          if Set.size classes == 1
            then Right ()
            else Left (CostChargeIncompatibleClass charge classes)
          if Set.size shapes == 1
            then Right ()
            else Left (CostChargeIncompatibleShape charge shapes)
          pure AttributedCost
            { attributedCostIdentity = charge
            , attributedCostClass = Set.findMin classes
            , attributedCostShape = Set.findMin shapes
            , attributedCostContributions = contributionIds
            , attributedCostRuntimeClaims = claims
            }

    lookupContribution identity = maybe
      (Left (CostContributionDomainMismatch
        (Map.keysSet contributionCharges)
        (Map.keysSet contributions)))
      Right
      (Map.lookup identity contributions)

deriveRuntimeSiteContributions
  :: Map CostContributionIdentity CostContribution
  -> Map RuntimeSiteKey CostContributionIdentity
deriveRuntimeSiteContributions contributions = Map.fromList
  [ (site, identity)
  | (identity, contribution) <- Map.toAscList contributions
  , RuntimeSiteCostMechanism site _ _ <-
      [costContributionMechanism contribution]
  ]

deriveClaimCharges
  :: Map CostContributionIdentity CostContribution
  -> Map CostContributionIdentity CostChargeIdentity
  -> Map RuntimeClaimRevision (Set CostChargeIdentity)
deriveClaimCharges contributions contributionCharges =
  Map.fromListWith Set.union
    [ (claim, Set.singleton charge)
    | (identity, contribution) <- Map.toAscList contributions
    , claim <- Set.toAscList
        (costContributionRuntimeClaims contribution)
    , Just charge <- [Map.lookup identity contributionCharges]
    ]

deriveStagingContributions
  :: Map CostContributionIdentity CostContribution
  -> Map StagingRequirementKey CostContributionIdentity
deriveStagingContributions contributions = Map.fromList
  [ (key, identity)
  | (identity, contribution) <- Map.toAscList contributions
  , StagingCostMechanism key <-
      [costContributionMechanism contribution]
  ]

deriveCostAttributionStageRevision
  :: CostAttributionStageBundle
  -> CostAttributionStageRevision
deriveCostAttributionStageRevision bundle = CostAttributionStageRevision
  ("phil.phase1.stage.cost-attribution.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom
          (unStagingEffectStageRevision
            (stagingEffectStageRevision (costAttributionStageBase bundle))))
      , ("runtime_bases", SemanticUnordered (Set.fromList
          [ semanticRuntimeBasis basis
          | (_, basis) <- Map.toAscList
              (costAttributionStageRuntimeBases bundle)
          ]))
      , ("contributions", SemanticUnordered (Set.fromList
          [ semanticCostContribution contribution
          | (_, contribution) <- Map.toAscList
              (costAttributionStageContributions bundle)
          ]))
      , ("contribution_charges", SemanticUnordered (Set.fromList
          [ SemanticRecord (Map.fromList
              [ ("contribution",
                  semanticContributionIdentity contribution)
              , ("charge", SemanticAtom
                  (unCostChargeIdentity charge))
              ])
          | (contribution, charge) <- Map.toAscList
              (costAttributionStageContributionCharges bundle)
          ]))
      , ("charges", SemanticUnordered (Set.fromList
          [ semanticAttributedCost charge
          | (_, charge) <- Map.toAscList
              (costAttributionStageCharges bundle)
          ]))
      , ("runtime_site_contributions",
          SemanticUnordered (Set.fromList
            [ SemanticRecord (Map.fromList
                [ ("site", semanticRuntimeSiteKey site)
                , ("contribution",
                    semanticContributionIdentity contribution)
                ])
            | (site, contribution) <- Map.toAscList
                (costAttributionStageRuntimeSiteContributions bundle)
            ]))
      , ("claim_charges", SemanticUnordered (Set.fromList
          [ SemanticRecord (Map.fromList
              [ ("claim", SemanticAtom (unRuntimeClaimRevision claim))
              , ("charges", SemanticUnordered
                  (Set.map
                    (SemanticAtom . unCostChargeIdentity)
                    charges))
              ])
          | (claim, charges) <- Map.toAscList
              (costAttributionStageClaimCharges bundle)
          ]))
      , ("staging_contributions",
          SemanticUnordered (Set.fromList
            [ SemanticRecord (Map.fromList
                [ ("staging", SemanticAtom
                    (unStagingRequirementKey key))
                , ("contribution",
                    semanticContributionIdentity contribution)
                ])
            | (key, contribution) <- Map.toAscList
                (costAttributionStageStagingContributions bundle)
            ]))
      ])))

makeCostAttributionStageBundle
  :: StagingEffectStageBundle
  -> Map RuntimePrimitiveProfileRef RuntimeCostBasis
  -> Map CostContributionIdentity CostContribution
  -> Map CostContributionIdentity CostChargeIdentity
  -> Map CostChargeIdentity AttributedCost
  -> Map RuntimeSiteKey CostContributionIdentity
  -> Map RuntimeClaimRevision (Set CostChargeIdentity)
  -> Map StagingRequirementKey CostContributionIdentity
  -> CostAttributionStageBundle
makeCostAttributionStageBundle
    base bases contributions contributionCharges charges
    siteContributions claimCharges stagingContributions =
  provisional
    { costAttributionStageRevision =
        deriveCostAttributionStageRevision provisional
    }
  where
    provisional = CostAttributionStageBundle
      { costAttributionStageBase = base
      , costAttributionStageRevision =
          CostAttributionStageRevision "pending"
      , costAttributionStageRuntimeBases = bases
      , costAttributionStageContributions = contributions
      , costAttributionStageContributionCharges = contributionCharges
      , costAttributionStageCharges = charges
      , costAttributionStageRuntimeSiteContributions = siteContributions
      , costAttributionStageClaimCharges = claimCharges
      , costAttributionStageStagingContributions = stagingContributions
      }

completeCostAttributionStageBundle
  :: StagingEffectStageBundle
  -> Map RuntimePrimitiveProfileRef RuntimeCostBasis
  -> Either String CostAttributionStageBundle
completeCostAttributionStageBundle base bases = do
  contributions <- mapLeft show
    (deriveExpectedCostContributions base bases)
  let contributionCharges =
        deriveContributionCharges bases contributions
  charges <- mapLeft show
    (deriveAttributedCosts contributions contributionCharges)
  let siteContributions =
        deriveRuntimeSiteContributions contributions
      claimCharges =
        deriveClaimCharges contributions contributionCharges
      stagingContributions =
        deriveStagingContributions contributions
  pure (makeCostAttributionStageBundle
    base bases contributions contributionCharges charges
    siteContributions claimCharges stagingContributions)

verifyCostAttributionStageBundle
  :: CostAttributionStageBundle
  -> Either CostAttributionVerificationError ()
verifyCostAttributionStageBundle bundle = do
  mapLeft CostAttributionBaseError $
    verifyStagingEffectStageBundle (costAttributionStageBase bundle)
  requireEqual CostAttributionStageRevisionMismatch
    (deriveCostAttributionStageRevision bundle)
    (costAttributionStageRevision bundle)

  validateRuntimeBases
    (costAttributionStageBase bundle)
    (costAttributionStageRuntimeBases bundle)

  expectedContributions <- deriveExpectedCostContributions
    (costAttributionStageBase bundle)
    (costAttributionStageRuntimeBases bundle)
  let actualContributions = costAttributionStageContributions bundle
  requireEqual CostContributionDomainMismatch
    (Map.keysSet expectedContributions)
    (Map.keysSet actualContributions)
  mapM_ (checkContribution actualContributions)
    (Map.toAscList expectedContributions)

  let expectedContributionCharges = deriveContributionCharges
        (costAttributionStageRuntimeBases bundle)
        expectedContributions
  requireEqual ContributionChargeMismatch
    expectedContributionCharges
    (costAttributionStageContributionCharges bundle)

  expectedCharges <- deriveAttributedCosts
    expectedContributions expectedContributionCharges
  let actualCharges = costAttributionStageCharges bundle
  requireEqual AttributedCostDomainMismatch
    (Map.keysSet expectedCharges)
    (Map.keysSet actualCharges)
  mapM_ (checkCharge actualCharges)
    (Map.toAscList expectedCharges)

  let expectedSites =
        deriveRuntimeSiteContributions expectedContributions
      expectedClaims =
        deriveClaimCharges
          expectedContributions expectedContributionCharges
      expectedStaging =
        deriveStagingContributions expectedContributions
  requireEqual RuntimeSiteContributionMismatch
    expectedSites
    (costAttributionStageRuntimeSiteContributions bundle)
  requireEqual RuntimeClaimChargeMismatch
    expectedClaims
    (costAttributionStageClaimCharges bundle)
  requireEqual StagingContributionMismatch
    expectedStaging
    (costAttributionStageStagingContributions bundle)

validateRuntimeBases
  :: StagingEffectStageBundle
  -> Map RuntimePrimitiveProfileRef RuntimeCostBasis
  -> Either CostAttributionVerificationError ()
validateRuntimeBases base bases = do
  let primitiveStage = stagingEffectStageBase base
      expectedProfiles = Set.fromList
        [ runtimePrimitiveSiteProfile binding
        | binding <- Map.elems
            (runtimePrimitiveStageSites primitiveStage)
        ]
      actualProfiles = Map.keysSet bases
  requireEqual RuntimeCostBasisDomainMismatch
    expectedProfiles actualProfiles
  mapM_ (checkBasis base) (Map.toAscList bases)

checkBasis
  :: StagingEffectStageBundle
  -> (RuntimePrimitiveProfileRef, RuntimeCostBasis)
  -> Either CostAttributionVerificationError ()
checkBasis base (profile, basis) = do
  requireEqual RuntimeCostBasisMapKeyMismatch
    profile (runtimeCostBasisProfile basis)
  decision <- maybe
    (Left (RuntimeCostBasisUnknownDecision
      profile (runtimeCostBasisDecision basis)))
    Right
    (Map.lookup
      (runtimeCostBasisDecision basis)
      (baseLoweringDecisions base))
  case loweringCostClass decision of
    Nothing -> Left (RuntimeCostBasisMissingClass
      profile (runtimeCostBasisDecision basis))
    Just _ -> Right ()
  if costShapeEmpty (loweringCostShape decision)
    then Left (RuntimeCostBasisEmptyShape
      profile (runtimeCostBasisDecision basis))
    else Right ()
  if Text.null
      (unCostChargeIdentity (runtimeCostBasisCharge basis))
    then Left (RuntimeCostBasisEmptyCharge profile)
    else Right ()

runtimeContribution
  :: StagingEffectStageBundle
  -> Map RuntimePrimitiveProfileRef RuntimeCostBasis
  -> (RuntimeSiteKey, RuntimePrimitiveSiteBinding)
  -> Either CostAttributionVerificationError
       (CostContributionIdentity, CostContribution)
runtimeContribution base bases (site, binding) = do
  let profile = runtimePrimitiveSiteProfile binding
  basis <- maybe
    (Left (RuntimeCostBasisDomainMismatch
      (Set.singleton profile) (Map.keysSet bases)))
    Right
    (Map.lookup profile bases)
  decision <- maybe
    (Left (RuntimeCostBasisUnknownDecision
      profile (runtimeCostBasisDecision basis)))
    Right
    (Map.lookup
      (runtimeCostBasisDecision basis)
      (baseLoweringDecisions base))
  costClass <- maybe
    (Left (RuntimeCostBasisMissingClass
      profile (runtimeCostBasisDecision basis)))
    Right
    (loweringCostClass decision)
  let identity = RuntimeCostContribution
        (runtimePrimitiveSiteCostIdentity binding)
      contribution = CostContribution
        { costContributionIdentity = identity
        , costContributionMechanism =
            RuntimeSiteCostMechanism
              site profile (runtimeCostBasisDecision basis)
        , costContributionClass = costClass
        , costContributionShape = loweringCostShape decision
        , costContributionRuntimeClaims =
            runtimePrimitiveSiteClaims binding
        }
  pure (identity, contribution)

stagingContribution
  :: (StagingRequirementKey, StagingEvent)
  -> Either CostAttributionVerificationError
       (CostContributionIdentity, CostContribution)
stagingContribution (key, event) = case stagingEventCost event of
  Nothing -> Left (StagingContributionMismatch
    (Map.singleton key
      (StagingCostContribution
        (StagingCostIdentity "missing")))
    Map.empty)
  Just cost ->
    let identity =
          StagingCostContribution (stagingCostIdentity cost)
        contribution = CostContribution
          { costContributionIdentity = identity
          , costContributionMechanism = StagingCostMechanism key
          , costContributionClass = stagingCostClass cost
          , costContributionShape = stagingCostShape cost
          , costContributionRuntimeClaims = Set.empty
          }
    in Right (identity, contribution)

checkContribution
  :: Map CostContributionIdentity CostContribution
  -> (CostContributionIdentity, CostContribution)
  -> Either CostAttributionVerificationError ()
checkContribution actual (identity, expected) =
  case Map.lookup identity actual of
    Nothing -> Left (CostContributionDomainMismatch
      (Set.singleton identity) (Map.keysSet actual))
    Just observed -> do
      requireEqual CostContributionMapKeyMismatch
        identity (costContributionIdentity observed)
      if expected == observed
        then Right ()
        else Left
          (CostContributionEntryMismatch identity expected observed)

checkCharge
  :: Map CostChargeIdentity AttributedCost
  -> (CostChargeIdentity, AttributedCost)
  -> Either CostAttributionVerificationError ()
checkCharge actual (identity, expected) =
  case Map.lookup identity actual of
    Nothing -> Left (AttributedCostDomainMismatch
      (Set.singleton identity) (Map.keysSet actual))
    Just observed -> do
      requireEqual AttributedCostMapKeyMismatch
        identity (attributedCostIdentity observed)
      if expected == observed
        then Right ()
        else Left
          (AttributedCostEntryMismatch identity expected observed)

baseLoweringDecisions
  :: StagingEffectStageBundle
  -> Map DecisionId LoweringDecision
baseLoweringDecisions =
  loweringLedgerDecisions
    . systemsArtifactLoweringLedger
    . phase1StageSystemsArtifact
    . subjectStageBase
    . evidenceTransferStageBase
    . evidenceErasureStageBase
    . assumptionDependencyStageBase
    . targetStrengtheningStageBase
    . runtimeClaimStageBase
    . runtimePrimitiveStageBase
    . stagingEffectStageBase

costShapeEmpty :: CostShape -> Bool
costShapeEmpty shape = all (== Nothing)
  [ costCompileTime shape
  , costCodeSize shape
  , costAllocationCount shape
  , costPeakLiveMemory shape
  , costBytesCopied shape
  , costDynamicCheckCount shape
  , costBranchOrDispatch shape
  , costHashOrCryptoWork shape
  , costSynchronization shape
  , costFrequency shape
  ]

duplicateKeys :: Ord a => [a] -> Set a
duplicateKeys values = Map.keysSet (Map.filter (> (1 :: Int)) counts)
  where
    counts = Map.fromListWith (+)
      [ (value, 1 :: Int)
      | value <- values
      ]

semanticRuntimeBasis :: RuntimeCostBasis -> SemanticForm
semanticRuntimeBasis basis = SemanticRecord (Map.fromList
  [ ("profile", SemanticAtom
      (unRuntimePrimitiveProfileRef
        (runtimeCostBasisProfile basis)))
  , ("decision", SemanticAtom
      (unDecisionId (runtimeCostBasisDecision basis)))
  , ("charge", SemanticAtom
      (unCostChargeIdentity (runtimeCostBasisCharge basis)))
  ])

semanticCostContribution :: CostContribution -> SemanticForm
semanticCostContribution contribution = SemanticRecord (Map.fromList
  [ ("identity", semanticContributionIdentity
      (costContributionIdentity contribution))
  , ("mechanism", semanticCostMechanism
      (costContributionMechanism contribution))
  , ("class", SemanticAtom
      (renderCostClass (costContributionClass contribution)))
  , ("shape", semanticCostShape
      (costContributionShape contribution))
  , ("runtime_claims", SemanticUnordered
      (Set.map
        (SemanticAtom . unRuntimeClaimRevision)
        (costContributionRuntimeClaims contribution)))
  ])

semanticAttributedCost :: AttributedCost -> SemanticForm
semanticAttributedCost charge = SemanticRecord (Map.fromList
  [ ("identity", SemanticAtom
      (unCostChargeIdentity (attributedCostIdentity charge)))
  , ("class", SemanticAtom
      (renderCostClass (attributedCostClass charge)))
  , ("shape", semanticCostShape
      (attributedCostShape charge))
  , ("contributions", SemanticUnordered
      (Set.map semanticContributionIdentity
        (attributedCostContributions charge)))
  , ("runtime_claims", SemanticUnordered
      (Set.map
        (SemanticAtom . unRuntimeClaimRevision)
        (attributedCostRuntimeClaims charge)))
  ])

semanticContributionIdentity
  :: CostContributionIdentity
  -> SemanticForm
semanticContributionIdentity identity = case identity of
  RuntimeCostContribution runtimeIdentity ->
    SemanticRecord (Map.fromList
      [ ("kind", SemanticAtom "runtime-site")
      , ("value", SemanticAtom
          (unPhysicalRuntimeCostIdentity runtimeIdentity))
      ])
  StagingCostContribution stagingIdentity ->
    SemanticRecord (Map.fromList
      [ ("kind", SemanticAtom "staging")
      , ("value", SemanticAtom
          (unStagingCostIdentity stagingIdentity))
      ])

semanticCostMechanism :: CostMechanism -> SemanticForm
semanticCostMechanism mechanism = case mechanism of
  RuntimeSiteCostMechanism site profile decision ->
    SemanticRecord (Map.fromList
      [ ("kind", SemanticAtom "runtime-site")
      , ("site", semanticRuntimeSiteKey site)
      , ("profile", SemanticAtom
          (unRuntimePrimitiveProfileRef profile))
      , ("decision", SemanticAtom (unDecisionId decision))
      ])
  StagingCostMechanism key ->
    SemanticRecord (Map.fromList
      [ ("kind", SemanticAtom "staging")
      , ("key", SemanticAtom
          (unStagingRequirementKey key))
      ])

semanticRuntimeSiteKey :: RuntimeSiteKey -> SemanticForm
semanticRuntimeSiteKey key = SemanticRecord (Map.fromList
  [ ("function", SemanticAtom (runtimeSiteFunction key))
  , ("block", SemanticAtom (unBlockId (runtimeSiteBlock key)))
  , ("slot", SemanticAtom
      (renderRuntimeSiteSlot (runtimeSiteSlot key)))
  ])

renderRuntimeSiteSlot :: RuntimeSiteSlot -> Text
renderRuntimeSiteSlot slot = case slot of
  RuntimeOperationSite index ->
    "op." <> Text.pack (show index)
  RuntimeTerminatorSite -> "term"

semanticCostShape :: CostShape -> SemanticForm
semanticCostShape shape = SemanticRecord (Map.fromList
  [ ("compile_time", semanticMaybeText (costCompileTime shape))
  , ("code_size", semanticMaybeText (costCodeSize shape))
  , ("allocation_count",
      semanticMaybeText (costAllocationCount shape))
  , ("peak_live_memory",
      semanticMaybeText (costPeakLiveMemory shape))
  , ("bytes_copied", semanticMaybeText (costBytesCopied shape))
  , ("dynamic_check_count",
      semanticMaybeText (costDynamicCheckCount shape))
  , ("branch_or_dispatch",
      semanticMaybeText (costBranchOrDispatch shape))
  , ("hash_or_crypto_work",
      semanticMaybeText (costHashOrCryptoWork shape))
  , ("synchronization",
      semanticMaybeText (costSynchronization shape))
  , ("frequency", semanticMaybeText (costFrequency shape))
  ])

semanticMaybeText :: Maybe Text -> SemanticForm
semanticMaybeText =
  maybe (SemanticAtom "none") SemanticAtom

renderCostClass :: CostClass -> Text
renderCostClass costClass = case costClass of
  SemanticRequired -> "semantic-required"
  RuntimeAssuranceRequired -> "runtime-assurance-required"
  TargetRequired -> "target-required"
  DefensiveProfile -> "defensive-profile"
  ConservativeLowering -> "conservative-lowering"

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
