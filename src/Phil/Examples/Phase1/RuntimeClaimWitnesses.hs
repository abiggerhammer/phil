{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.RuntimeClaimWitnesses
  ( uploadRuntimeClaimStage
  , steveRuntimeClaimStage
  , uploadCompositeClaimRevision
  , completeRuntimeClaimStage
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Assurance.Types (RevisionId (..))
import Phil.Examples.Phase1.TargetStrengtheningWitnesses
  ( steveTargetStrengtheningStage
  , uploadTargetStrengtheningStage
  )
import Phil.Systems.IR
  ( RuntimeSiteKind (..)
  , RuntimeSiteRef (..)
  )
import Phil.Systems.RuntimeClaimBinding
import Phil.Systems.TargetStrengthening
  ( TargetStrengtheningStageBundle
  )

uploadCompositeClaimRevision :: RuntimeClaimRevision
uploadCompositeClaimRevision =
  RuntimeClaimRevision "claim.phase1.upload.payload-integrity-chain.v1"

uploadRuntimeClaimStage :: Either String RuntimeClaimStageBundle
uploadRuntimeClaimStage = do
  let base = uploadTargetStrengtheningStage
      sites = deriveRuntimeSiteBindings base
      (nativeClaims, nativeBindings) = nativeRuntimeClaims base sites
  receiveSite <- uniqueSiteByKind ExactReceiveBoundary sites
  digestSite <- uniqueSiteByKind DigestBoundary sites
  let compositeSites = Set.fromList [receiveSite, digestSite]
      compositeObligations = Set.fromList
        [ runtimeSiteRevision (runtimeSiteBindingRef binding)
        | site <- Set.toAscList compositeSites
        , Just binding <- [Map.lookup site sites]
        ]
      compositeClaim = RuntimeClaim
        { runtimeClaimRevision = uploadCompositeClaimRevision
        , runtimeClaimSourceObligations = compositeObligations
        , runtimeClaimSourceFacts =
            deriveRuntimeClaimSourceFacts base compositeObligations
        , runtimeClaimSemanticSubjects = Set.singleton "upload.payload"
        }
      compositeBinding = RuntimeClaimBinding
        { runtimeClaimBindingRevision = uploadCompositeClaimRevision
        , runtimeClaimBindingSites = compositeSites
        , runtimeClaimBindingCostIdentities = costIdentitiesFor sites compositeSites
        }
      claims = Map.insert uploadCompositeClaimRevision compositeClaim nativeClaims
      bindings = Map.insert uploadCompositeClaimRevision compositeBinding nativeBindings
  pure (completeRuntimeClaimStage base claims bindings)

steveRuntimeClaimStage :: Either String RuntimeClaimStageBundle
steveRuntimeClaimStage = do
  base <- steveTargetStrengtheningStage
  let sites = deriveRuntimeSiteBindings base
      (claims, bindings) = nativeRuntimeClaims base sites
  pure (completeRuntimeClaimStage base claims bindings)

completeRuntimeClaimStage
  :: TargetStrengtheningStageBundle
  -> Map RuntimeClaimRevision RuntimeClaim
  -> Map RuntimeClaimRevision RuntimeClaimBinding
  -> RuntimeClaimStageBundle
completeRuntimeClaimStage = completeRuntimeClaimStageBundle

nativeRuntimeClaims
  :: TargetStrengtheningStageBundle
  -> Map RuntimeSiteKey RuntimeSiteBinding
  -> ( Map RuntimeClaimRevision RuntimeClaim
     , Map RuntimeClaimRevision RuntimeClaimBinding
     )
nativeRuntimeClaims base sites = (claims, bindings)
  where
    grouped = Map.fromListWith Set.union
      [ ( runtimeSiteRevision (runtimeSiteBindingRef siteBinding)
        , Set.singleton siteKey
        )
      | (siteKey, siteBinding) <- Map.toAscList sites
      ]

    claims = Map.fromList
      [ (claimRevision, RuntimeClaim
          { runtimeClaimRevision = claimRevision
          , runtimeClaimSourceObligations = Set.singleton obligationRevision
          , runtimeClaimSourceFacts = deriveRuntimeClaimSourceFacts
              base (Set.singleton obligationRevision)
          , runtimeClaimSemanticSubjects = Set.empty
          })
      | (obligationRevision, _) <- Map.toAscList grouped
      , let claimRevision = nativeClaimRevision obligationRevision
      ]

    bindings = Map.fromList
      [ (claimRevision, RuntimeClaimBinding
          { runtimeClaimBindingRevision = claimRevision
          , runtimeClaimBindingSites = siteKeys
          , runtimeClaimBindingCostIdentities = costIdentitiesFor sites siteKeys
          })
      | (obligationRevision, siteKeys) <- Map.toAscList grouped
      , let claimRevision = nativeClaimRevision obligationRevision
      ]

nativeClaimRevision :: RevisionId -> RuntimeClaimRevision
nativeClaimRevision revision = RuntimeClaimRevision
  ("claim.native:" <> unRevisionId revision)

costIdentitiesFor
  :: Map RuntimeSiteKey RuntimeSiteBinding
  -> Set RuntimeSiteKey
  -> Set PhysicalRuntimeCostIdentity
costIdentitiesFor sites siteKeys = Set.fromList
  [ runtimeSiteBindingCostIdentity binding
  | site <- Set.toAscList siteKeys
  , Just binding <- [Map.lookup site sites]
  ]

uniqueSiteByKind
  :: RuntimeSiteKind
  -> Map RuntimeSiteKey RuntimeSiteBinding
  -> Either String RuntimeSiteKey
uniqueSiteByKind kind sites = case
  [ key
  | (key, binding) <- Map.toAscList sites
  , runtimeSiteKind (runtimeSiteBindingRef binding) == kind
  ] of
  [key] -> Right key
  [] -> Left ("no runtime site found for kind " <> show kind)
  keys -> Left ("multiple runtime sites found for kind " <> show kind
    <> ": " <> show keys)
