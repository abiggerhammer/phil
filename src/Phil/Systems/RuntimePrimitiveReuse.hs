{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveStageRevision (..)
  , RuntimePrimitiveProfileRef (..)
  , RuntimePrimitiveSubjectRef (..)
  , RuntimePrimitiveSiteBinding (..)
  , RuntimePrimitiveStageBundle (..)
  , RuntimePrimitiveVerificationError (..)
  , deriveRuntimePrimitiveSiteBindings
  , deriveRuntimePrimitiveReverse
  , deriveRuntimePrimitiveStageRevision
  , makeRuntimePrimitiveStageBundle
  , completeRuntimePrimitiveStageBundle
  , verifyRuntimePrimitiveStageBundle
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
import Phil.Systems.IR
  ( BlockId (..)
  , RuntimeSiteRef (..)
  )
import Phil.Systems.Phase1Stage
  ( SourceFactKey (..)
  )
import Phil.Systems.RuntimeClaimBinding

newtype RuntimePrimitiveStageRevision = RuntimePrimitiveStageRevision
  { unRuntimePrimitiveStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Bounded Phase-1 implementation-family/profile identity.  The predecessor
-- RuntimeSiteRef already carries an exact reusable lower-stage token in
-- runtimeSiteCostRef.  SYS-016 treats that token as the current primitive/profile
-- key while keeping SYS-015's physical cost identity site-owned and separate.
newtype RuntimePrimitiveProfileRef = RuntimePrimitiveProfileRef
  { unRuntimePrimitiveProfileRef :: Text
  }
  deriving (Eq, Ord, Show)

-- | The exact semantic subject basis visible at the SYS-015 boundary.  Explicit
-- claim subjects are retained when present; otherwise exact source-fact subjects
-- keep distinct claim semantics from disappearing merely because one primitive
-- implementation is reused.
data RuntimePrimitiveSubjectRef
  = RuntimePrimitiveExplicitSubject Text
  | RuntimePrimitiveSourceFactSubject SourceFactKey
  deriving (Eq, Ord, Show)

-- | One exact runtime-site occurrence projected onto its reusable primitive
-- profile while retaining every identity that must not collapse with that
-- profile: site, claims, semantic subjects, and physical cost.
data RuntimePrimitiveSiteBinding = RuntimePrimitiveSiteBinding
  { runtimePrimitiveSiteKey :: RuntimeSiteKey
  , runtimePrimitiveSiteProfile :: RuntimePrimitiveProfileRef
  , runtimePrimitiveSiteClaims :: Set RuntimeClaimRevision
  , runtimePrimitiveSiteSubjects :: Set RuntimePrimitiveSubjectRef
  , runtimePrimitiveSiteCostIdentity :: PhysicalRuntimeCostIdentity
  }
  deriving (Eq, Ord, Show)

data RuntimePrimitiveStageBundle = RuntimePrimitiveStageBundle
  { runtimePrimitiveStageBase :: RuntimeClaimStageBundle
  , runtimePrimitiveStageRevision :: RuntimePrimitiveStageRevision
  , runtimePrimitiveStageSites :: Map RuntimeSiteKey RuntimePrimitiveSiteBinding
  , runtimePrimitiveStageReverse
      :: Map RuntimePrimitiveProfileRef (Set RuntimeSiteKey)
  }
  deriving (Eq, Show)

data RuntimePrimitiveVerificationError
  = RuntimePrimitiveBaseError RuntimeClaimVerificationError
  | RuntimePrimitiveStageRevisionMismatch
      RuntimePrimitiveStageRevision RuntimePrimitiveStageRevision
  | RuntimePrimitiveSiteDomainMismatch
      (Set RuntimeSiteKey) (Set RuntimeSiteKey)
  | RuntimePrimitiveSiteKeyMismatch RuntimeSiteKey RuntimeSiteKey
  | RuntimePrimitiveEmptyProfile RuntimeSiteKey
  | RuntimePrimitiveProfileMismatch
      RuntimeSiteKey RuntimePrimitiveProfileRef RuntimePrimitiveProfileRef
  | RuntimePrimitiveClaimIdentityMismatch
      RuntimeSiteKey (Set RuntimeClaimRevision) (Set RuntimeClaimRevision)
  | RuntimePrimitiveSubjectIdentityMismatch
      RuntimeSiteKey
      (Set RuntimePrimitiveSubjectRef)
      (Set RuntimePrimitiveSubjectRef)
  | RuntimePrimitiveCostIdentityMismatch
      RuntimeSiteKey PhysicalRuntimeCostIdentity PhysicalRuntimeCostIdentity
  | RuntimePrimitiveReverseDomainMismatch
      (Set RuntimePrimitiveProfileRef) (Set RuntimePrimitiveProfileRef)
  | RuntimePrimitiveReverseSitesMismatch
      RuntimePrimitiveProfileRef (Set RuntimeSiteKey) (Set RuntimeSiteKey)
  | RuntimePrimitiveSharedCostIdentityCollapse
      RuntimePrimitiveProfileRef
      (Set RuntimeSiteKey)
      (Set PhysicalRuntimeCostIdentity)
  deriving (Eq, Show)

deriveRuntimePrimitiveSiteBindings
  :: RuntimeClaimStageBundle
  -> Map RuntimeSiteKey RuntimePrimitiveSiteBinding
deriveRuntimePrimitiveSiteBindings base = Map.fromList
  [ (siteKey, bindingFor siteKey siteBinding)
  | (siteKey, siteBinding) <- Map.toAscList (runtimeClaimStageSites base)
  ]
  where
    bindingFor siteKey siteBinding = RuntimePrimitiveSiteBinding
      { runtimePrimitiveSiteKey = siteKey
      , runtimePrimitiveSiteProfile = RuntimePrimitiveProfileRef
          (runtimeSiteCostRef (runtimeSiteBindingRef siteBinding))
      , runtimePrimitiveSiteClaims = claimsAt siteKey
      , runtimePrimitiveSiteSubjects = subjectsAt siteKey
      , runtimePrimitiveSiteCostIdentity =
          runtimeSiteBindingCostIdentity siteBinding
      }

    claimsAt siteKey = Map.findWithDefault Set.empty siteKey
      (runtimeClaimStageReverse base)

    subjectsAt siteKey = Set.unions
      [ claimSubjects claim
      | claimRevision <- Set.toAscList (claimsAt siteKey)
      , Just claim <- [Map.lookup claimRevision (runtimeClaimStageClaims base)]
      ]

    claimSubjects claim = Set.union
      (Set.map RuntimePrimitiveExplicitSubject
        (runtimeClaimSemanticSubjects claim))
      (Set.map RuntimePrimitiveSourceFactSubject
        (runtimeClaimSourceFacts claim))

deriveRuntimePrimitiveReverse
  :: Map RuntimeSiteKey RuntimePrimitiveSiteBinding
  -> Map RuntimePrimitiveProfileRef (Set RuntimeSiteKey)
deriveRuntimePrimitiveReverse bindings = Map.fromListWith Set.union
  [ (runtimePrimitiveSiteProfile binding, Set.singleton siteKey)
  | (siteKey, binding) <- Map.toAscList bindings
  ]

deriveRuntimePrimitiveStageRevision
  :: RuntimePrimitiveStageBundle
  -> RuntimePrimitiveStageRevision
deriveRuntimePrimitiveStageRevision bundle = RuntimePrimitiveStageRevision
  ("phil.phase1.stage.runtime-primitive-reuse.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom
          (unRuntimeClaimStageRevision
            (runtimeClaimStageRevision (runtimePrimitiveStageBase bundle))))
      , ("sites", SemanticUnordered (Set.fromList
          [ semanticSiteBinding binding
          | (_, binding) <- Map.toAscList (runtimePrimitiveStageSites bundle)
          ]))
      , ("reverse", SemanticUnordered (Set.fromList
          [ SemanticRecord (Map.fromList
              [ ("profile", SemanticAtom
                  (unRuntimePrimitiveProfileRef profile))
              , ("sites", SemanticUnordered
                  (Set.map semanticSiteKey sites))
              ])
          | (profile, sites) <- Map.toAscList
              (runtimePrimitiveStageReverse bundle)
          ]))
      ])))

makeRuntimePrimitiveStageBundle
  :: RuntimeClaimStageBundle
  -> Map RuntimeSiteKey RuntimePrimitiveSiteBinding
  -> Map RuntimePrimitiveProfileRef (Set RuntimeSiteKey)
  -> RuntimePrimitiveStageBundle
makeRuntimePrimitiveStageBundle base sites reverse = provisional
  { runtimePrimitiveStageRevision =
      deriveRuntimePrimitiveStageRevision provisional }
  where
    provisional = RuntimePrimitiveStageBundle
      { runtimePrimitiveStageBase = base
      , runtimePrimitiveStageRevision = RuntimePrimitiveStageRevision "pending"
      , runtimePrimitiveStageSites = sites
      , runtimePrimitiveStageReverse = reverse
      }

completeRuntimePrimitiveStageBundle
  :: RuntimeClaimStageBundle
  -> RuntimePrimitiveStageBundle
completeRuntimePrimitiveStageBundle base =
  makeRuntimePrimitiveStageBundle base sites reverse
  where
    sites = deriveRuntimePrimitiveSiteBindings base
    reverse = deriveRuntimePrimitiveReverse sites

verifyRuntimePrimitiveStageBundle
  :: RuntimePrimitiveStageBundle
  -> Either RuntimePrimitiveVerificationError ()
verifyRuntimePrimitiveStageBundle bundle = do
  mapLeft RuntimePrimitiveBaseError $
    verifyRuntimeClaimStageBundle (runtimePrimitiveStageBase bundle)
  requireEqual RuntimePrimitiveStageRevisionMismatch
    (deriveRuntimePrimitiveStageRevision bundle)
    (runtimePrimitiveStageRevision bundle)

  let expectedSites = deriveRuntimePrimitiveSiteBindings
        (runtimePrimitiveStageBase bundle)
      actualSites = runtimePrimitiveStageSites bundle
  requireEqual RuntimePrimitiveSiteDomainMismatch
    (Map.keysSet expectedSites) (Map.keysSet actualSites)
  mapM_ checkBasicBinding (Map.toAscList actualSites)

  let expectedReverse = deriveRuntimePrimitiveReverse actualSites
      actualReverse = runtimePrimitiveStageReverse bundle
  requireEqual RuntimePrimitiveReverseDomainMismatch
    (Map.keysSet expectedReverse) (Map.keysSet actualReverse)
  mapM_ (checkReverse actualReverse) (Map.toAscList expectedReverse)

  -- Run the explicit shared-primitive physical-cost separation check before
  -- field-by-field equality so a cost-collapse mutation is diagnosed at the
  -- competence boundary established by SYS-016 rather than as a generic field
  -- mismatch.
  mapM_ (checkSharedCostIdentitySeparation actualSites)
    (Map.toAscList actualReverse)

  mapM_ (checkExpectedBinding actualSites) (Map.toAscList expectedSites)

checkBasicBinding
  :: (RuntimeSiteKey, RuntimePrimitiveSiteBinding)
  -> Either RuntimePrimitiveVerificationError ()
checkBasicBinding (key, binding) = do
  requireEqual RuntimePrimitiveSiteKeyMismatch
    key (runtimePrimitiveSiteKey binding)
  if Text.null (unRuntimePrimitiveProfileRef
      (runtimePrimitiveSiteProfile binding))
    then Left (RuntimePrimitiveEmptyProfile key)
    else Right ()

checkExpectedBinding
  :: Map RuntimeSiteKey RuntimePrimitiveSiteBinding
  -> (RuntimeSiteKey, RuntimePrimitiveSiteBinding)
  -> Either RuntimePrimitiveVerificationError ()
checkExpectedBinding actualSites (key, expected) = case Map.lookup key actualSites of
  Nothing -> Left (RuntimePrimitiveSiteDomainMismatch
    (Set.singleton key) Set.empty)
  Just actual -> do
    requireEqual (RuntimePrimitiveProfileMismatch key)
      (runtimePrimitiveSiteProfile expected)
      (runtimePrimitiveSiteProfile actual)
    requireEqual (RuntimePrimitiveClaimIdentityMismatch key)
      (runtimePrimitiveSiteClaims expected)
      (runtimePrimitiveSiteClaims actual)
    requireEqual (RuntimePrimitiveSubjectIdentityMismatch key)
      (runtimePrimitiveSiteSubjects expected)
      (runtimePrimitiveSiteSubjects actual)
    requireEqual (RuntimePrimitiveCostIdentityMismatch key)
      (runtimePrimitiveSiteCostIdentity expected)
      (runtimePrimitiveSiteCostIdentity actual)

checkReverse
  :: Map RuntimePrimitiveProfileRef (Set RuntimeSiteKey)
  -> (RuntimePrimitiveProfileRef, Set RuntimeSiteKey)
  -> Either RuntimePrimitiveVerificationError ()
checkReverse actualReverse (profile, expected) =
  requireEqual (RuntimePrimitiveReverseSitesMismatch profile)
    expected (Map.findWithDefault Set.empty profile actualReverse)

checkSharedCostIdentitySeparation
  :: Map RuntimeSiteKey RuntimePrimitiveSiteBinding
  -> (RuntimePrimitiveProfileRef, Set RuntimeSiteKey)
  -> Either RuntimePrimitiveVerificationError ()
checkSharedCostIdentitySeparation bindings (profile, sites)
  | Set.size sites <= 1 = Right ()
  | Set.size costs == Set.size sites = Right ()
  | otherwise = Left (RuntimePrimitiveSharedCostIdentityCollapse
      profile sites costs)
  where
    costs = Set.fromList
      [ runtimePrimitiveSiteCostIdentity binding
      | site <- Set.toAscList sites
      , Just binding <- [Map.lookup site bindings]
      ]

semanticSiteBinding :: RuntimePrimitiveSiteBinding -> SemanticForm
semanticSiteBinding binding = SemanticRecord (Map.fromList
  [ ("site", semanticSiteKey (runtimePrimitiveSiteKey binding))
  , ("profile", SemanticAtom
      (unRuntimePrimitiveProfileRef (runtimePrimitiveSiteProfile binding)))
  , ("claims", SemanticUnordered
      (Set.map
        (SemanticAtom . unRuntimeClaimRevision)
        (runtimePrimitiveSiteClaims binding)))
  , ("subjects", SemanticUnordered
      (Set.map semanticSubjectRef (runtimePrimitiveSiteSubjects binding)))
  , ("physical_cost", SemanticAtom
      (unPhysicalRuntimeCostIdentity
        (runtimePrimitiveSiteCostIdentity binding)))
  ])

semanticSubjectRef :: RuntimePrimitiveSubjectRef -> SemanticForm
semanticSubjectRef subject = case subject of
  RuntimePrimitiveExplicitSubject value -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "explicit")
    , ("value", SemanticAtom value)
    ])
  RuntimePrimitiveSourceFactSubject fact -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "source-fact")
    , ("value", SemanticAtom (unSourceFactKey fact))
    ])

semanticSiteKey :: RuntimeSiteKey -> SemanticForm
semanticSiteKey key = SemanticRecord (Map.fromList
  [ ("function", SemanticAtom (runtimeSiteFunction key))
  , ("block", SemanticAtom (unBlockId (runtimeSiteBlock key)))
  , ("slot", SemanticAtom (renderSiteSlot (runtimeSiteSlot key)))
  ])

renderSiteSlot :: RuntimeSiteSlot -> Text
renderSiteSlot slot = case slot of
  RuntimeOperationSite index -> "op." <> Text.pack (show index)
  RuntimeTerminatorSite -> "term"

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
