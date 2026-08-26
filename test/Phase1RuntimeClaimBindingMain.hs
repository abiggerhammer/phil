{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.Types (RevisionId (..))
import Phil.Examples.Phase1.RuntimeClaimWitnesses
import Phil.Examples.Phase1.TargetStrengtheningWitnesses
  ( steveTargetStrengtheningStage
  , uploadTargetStrengtheningStage
  )
import Phil.Systems.IR (BlockId (..))
import Phil.Systems.RuntimeClaimBinding
import Phil.Systems.TargetStrengthening
  ( verifyTargetStrengtheningStageBundle
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-015 SYS-014 upload predecessor remains valid" uploadTargetRegression
    , test "SYS-015 SYS-014 Steve predecessor remains valid" steveTargetRegression
    , test "SYS-015 upload many-to-many runtime claim relation is accepted" uploadManyToManyAccepted
    , test "SYS-015 Steve with no modeled runtime sites is accepted" steveEmptyAccepted
    , test "SYS-015 one claim may require several runtime sites" multiSiteClaimPresent
    , test "SYS-015 one runtime site may support several claims" multiClaimSitePresent
    , test "SYS-015 multi-site claim cannot silently omit a required site" multiSiteOmissionRejected
    , test "SYS-015 every modeled runtime site must support at least one claim" unclaimedSiteRejected
    , test "SYS-015 reverse site-to-claim relation is exact" reverseOmissionRejected
    , test "SYS-015 claim retains exact physical cost identities" claimCostMismatchRejected
    , test "SYS-015 physical cost registry cannot omit a live site cost" costRegistryOmissionRejected
    , test "SYS-015 physical site cost cannot be duplicated under an alias" duplicateCostAliasRejected
    , test "SYS-015 claim cannot cite an unknown runtime site" unknownSiteRejected
    , test "SYS-015 claim retains exact source-fact basis" sourceFactMismatchRejected
    , test "SYS-015 claim source obligations equal bound-site obligations" obligationMismatchRejected
    , test "SYS-015 runtime site registry is derived from the exact Systems graph" siteRegistryTamperRejected
    , test "SYS-015 runtime-claim stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadTargetRegression :: Either String ()
uploadTargetRegression = mapLeft show
  (verifyTargetStrengtheningStageBundle uploadTargetStrengtheningStage)

steveTargetRegression :: Either String ()
steveTargetRegression = do
  bundle <- steveTargetStrengtheningStage
  mapLeft show (verifyTargetStrengtheningStageBundle bundle)

uploadManyToManyAccepted :: Either String ()
uploadManyToManyAccepted = do
  bundle <- uploadRuntimeClaimStage
  mapLeft show (verifyRuntimeClaimStageBundle bundle)

steveEmptyAccepted :: Either String ()
steveEmptyAccepted = do
  bundle <- steveRuntimeClaimStage
  mapLeft show (verifyRuntimeClaimStageBundle bundle)

multiSiteClaimPresent :: Either String ()
multiSiteClaimPresent = do
  bundle <- uploadRuntimeClaimStage
  binding <- requireCompositeBinding bundle
  assert
    (Set.size (runtimeClaimBindingSites binding) >= 2)
    "composite upload claim does not span multiple runtime sites"

multiClaimSitePresent :: Either String ()
multiClaimSitePresent = do
  bundle <- uploadRuntimeClaimStage
  assert
    (any ((>= 2) . Set.size) (Map.elems (runtimeClaimStageReverse bundle)))
    "no runtime site supports multiple exact claims"

multiSiteOmissionRejected :: Either String ()
multiSiteOmissionRejected = do
  original <- uploadRuntimeClaimStage
  binding <- requireCompositeBinding original
  removed <- pickOne "composite site" (runtimeClaimBindingSites binding)
  let badBinding = binding
        { runtimeClaimBindingSites = Set.delete removed
            (runtimeClaimBindingSites binding)
        }
      bindings = Map.insert uploadCompositeClaimRevision badBinding
        (runtimeClaimStageBindings original)
      mutated = rebuild original
        (runtimeClaimStageSites original)
        (runtimeClaimStageClaims original)
        bindings
        (runtimeClaimStageReverse original)
        (runtimeClaimStagePhysicalCosts original)
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeClaimObligationSiteMismatch claim expected actual)
      | claim == uploadCompositeClaimRevision
          && expected /= actual -> Right ()
    other -> Left ("multi-site claim omission was accepted: " <> show other)

unclaimedSiteRejected :: Either String ()
unclaimedSiteRejected = do
  original <- uploadRuntimeClaimStage
  (site, claimsAtSite) <- pickSingletonClaimSite original
  onlyClaim <- pickOne "sole claim" claimsAtSite
  let claims = Map.delete onlyClaim (runtimeClaimStageClaims original)
      bindings = Map.delete onlyClaim (runtimeClaimStageBindings original)
      mutated = rebuild original
        (runtimeClaimStageSites original)
        claims
        bindings
        (runtimeClaimStageReverse original)
        (runtimeClaimStagePhysicalCosts original)
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeSiteUnclaimed actual) | actual == site -> Right ()
    other -> Left ("unclaimed runtime site was accepted: " <> show other)

reverseOmissionRejected :: Either String ()
reverseOmissionRejected = do
  original <- uploadRuntimeClaimStage
  binding <- requireCompositeBinding original
  site <- pickOne "composite site" (runtimeClaimBindingSites binding)
  let originalClaims = Map.findWithDefault Set.empty site
        (runtimeClaimStageReverse original)
      badReverse = Map.insert site
        (Set.delete uploadCompositeClaimRevision originalClaims)
        (runtimeClaimStageReverse original)
      mutated = rebuild original
        (runtimeClaimStageSites original)
        (runtimeClaimStageClaims original)
        (runtimeClaimStageBindings original)
        badReverse
        (runtimeClaimStagePhysicalCosts original)
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeClaimReverseClaimsMismatch actual expected observed)
      | actual == site
          && Set.member uploadCompositeClaimRevision expected
          && not (Set.member uploadCompositeClaimRevision observed) -> Right ()
    other -> Left ("reverse claim omission was accepted: " <> show other)

claimCostMismatchRejected :: Either String ()
claimCostMismatchRejected = do
  original <- uploadRuntimeClaimStage
  binding <- requireCompositeBinding original
  let invented = PhysicalRuntimeCostIdentity "runtime-cost.invented-per-claim"
      badBinding = binding
        { runtimeClaimBindingCostIdentities = Set.insert invented
            (runtimeClaimBindingCostIdentities binding)
        }
      bindings = Map.insert uploadCompositeClaimRevision badBinding
        (runtimeClaimStageBindings original)
      mutated = rebuild original
        (runtimeClaimStageSites original)
        (runtimeClaimStageClaims original)
        bindings
        (runtimeClaimStageReverse original)
        (runtimeClaimStagePhysicalCosts original)
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeClaimCostIdentityMismatch claim expected actual)
      | claim == uploadCompositeClaimRevision
          && not (Set.member invented expected)
          && Set.member invented actual -> Right ()
    other -> Left ("claim-local duplicate cost identity was accepted: " <> show other)

costRegistryOmissionRejected :: Either String ()
costRegistryOmissionRejected = do
  original <- uploadRuntimeClaimStage
  (costIdentity, _) <- pickMapEntry "physical runtime cost"
    (runtimeClaimStagePhysicalCosts original)
  let costs = Map.delete costIdentity (runtimeClaimStagePhysicalCosts original)
      mutated = rebuild original
        (runtimeClaimStageSites original)
        (runtimeClaimStageClaims original)
        (runtimeClaimStageBindings original)
        (runtimeClaimStageReverse original)
        costs
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeCostRegistryDomainMismatch expected actual)
      | Set.member costIdentity expected
          && not (Set.member costIdentity actual) -> Right ()
    other -> Left ("physical cost registry omission was accepted: " <> show other)

duplicateCostAliasRejected :: Either String ()
duplicateCostAliasRejected = do
  original <- uploadRuntimeClaimStage
  (_, cost) <- pickMapEntry "physical runtime cost"
    (runtimeClaimStagePhysicalCosts original)
  let alias = PhysicalRuntimeCostIdentity "runtime-cost.duplicate-alias"
      duplicated = cost { physicalRuntimeCostIdentity = alias }
      costs = Map.insert alias duplicated (runtimeClaimStagePhysicalCosts original)
      mutated = rebuild original
        (runtimeClaimStageSites original)
        (runtimeClaimStageClaims original)
        (runtimeClaimStageBindings original)
        (runtimeClaimStageReverse original)
        costs
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeCostRegistryDomainMismatch expected actual)
      | not (Set.member alias expected)
          && Set.member alias actual -> Right ()
    other -> Left ("duplicate physical cost alias was accepted: " <> show other)

unknownSiteRejected :: Either String ()
unknownSiteRejected = do
  original <- uploadRuntimeClaimStage
  binding <- requireCompositeBinding original
  removed <- pickOne "composite site" (runtimeClaimBindingSites binding)
  let invented = RuntimeSiteKey
        "UnknownFunction" (BlockId "unknown.block") RuntimeTerminatorSite
      badBinding = binding
        { runtimeClaimBindingSites = Set.insert invented
            (Set.delete removed (runtimeClaimBindingSites binding))
        }
      bindings = Map.insert uploadCompositeClaimRevision badBinding
        (runtimeClaimStageBindings original)
      mutated = rebuild original
        (runtimeClaimStageSites original)
        (runtimeClaimStageClaims original)
        bindings
        (runtimeClaimStageReverse original)
        (runtimeClaimStagePhysicalCosts original)
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeClaimUnknownSites claim unknown)
      | claim == uploadCompositeClaimRevision
          && Set.member invented unknown -> Right ()
    other -> Left ("unknown runtime site was accepted: " <> show other)

sourceFactMismatchRejected :: Either String ()
sourceFactMismatchRejected = do
  original <- uploadRuntimeClaimStage
  claim <- requireCompositeClaim original
  let badClaim = claim { runtimeClaimSourceFacts = Set.empty }
      claims = Map.insert uploadCompositeClaimRevision badClaim
        (runtimeClaimStageClaims original)
      mutated = rebuild original
        (runtimeClaimStageSites original)
        claims
        (runtimeClaimStageBindings original)
        (runtimeClaimStageReverse original)
        (runtimeClaimStagePhysicalCosts original)
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeClaimSourceFactMismatch actual expected observed)
      | actual == uploadCompositeClaimRevision
          && not (Set.null expected)
          && Set.null observed -> Right ()
    other -> Left ("runtime claim lost its exact source-fact basis: " <> show other)

obligationMismatchRejected :: Either String ()
obligationMismatchRejected = do
  original <- uploadRuntimeClaimStage
  claim <- requireCompositeClaim original
  removed <- pickOne "composite source obligation"
    (runtimeClaimSourceObligations claim)
  let badClaim = claim
        { runtimeClaimSourceObligations = Set.delete removed
            (runtimeClaimSourceObligations claim)
        }
      claims = Map.insert uploadCompositeClaimRevision badClaim
        (runtimeClaimStageClaims original)
      mutated = rebuild original
        (runtimeClaimStageSites original)
        claims
        (runtimeClaimStageBindings original)
        (runtimeClaimStageReverse original)
        (runtimeClaimStagePhysicalCosts original)
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeClaimObligationSiteMismatch actual expected observed)
      | actual == uploadCompositeClaimRevision
          && Set.member removed expected
          && not (Set.member removed observed) -> Right ()
    other -> Left ("claim/site obligation mismatch was accepted: " <> show other)

siteRegistryTamperRejected :: Either String ()
siteRegistryTamperRejected = do
  original <- uploadRuntimeClaimStage
  (site, binding) <- pickMapEntry "runtime site" (runtimeClaimStageSites original)
  let badBinding = binding
        { runtimeSiteBindingCostIdentity =
            PhysicalRuntimeCostIdentity "runtime-cost.wrong-site-identity"
        }
      sites = Map.insert site badBinding (runtimeClaimStageSites original)
      mutated = rebuild original
        sites
        (runtimeClaimStageClaims original)
        (runtimeClaimStageBindings original)
        (runtimeClaimStageReverse original)
        (runtimeClaimStagePhysicalCosts original)
  case verifyRuntimeClaimStageBundle mutated of
    Left (RuntimeSiteBindingMismatch actual expected observed)
      | actual == site && expected /= observed -> Right ()
    other -> Left ("tampered runtime-site registry was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- uploadRuntimeClaimStage
  let reverseMap mapValue = Map.fromList (reverse (Map.toAscList mapValue))
      rebuilt = makeRuntimeClaimStageBundle
        (runtimeClaimStageBase original)
        (reverseMap (runtimeClaimStageSites original))
        (reverseMap (runtimeClaimStageClaims original))
        (reverseMap (runtimeClaimStageBindings original))
        (reverseMap (runtimeClaimStageReverse original))
        (reverseMap (runtimeClaimStagePhysicalCosts original))
  assert
    (runtimeClaimStageRevision original == runtimeClaimStageRevision rebuilt)
    "runtime-claim revision changed with map/set enumeration order"
  mapLeft show (verifyRuntimeClaimStageBundle rebuilt)

requireCompositeClaim :: RuntimeClaimStageBundle -> Either String RuntimeClaim
requireCompositeClaim bundle = maybe
  (Left "upload composite runtime claim missing")
  Right
  (Map.lookup uploadCompositeClaimRevision (runtimeClaimStageClaims bundle))

requireCompositeBinding :: RuntimeClaimStageBundle -> Either String RuntimeClaimBinding
requireCompositeBinding bundle = maybe
  (Left "upload composite runtime claim binding missing")
  Right
  (Map.lookup uploadCompositeClaimRevision (runtimeClaimStageBindings bundle))

pickSingletonClaimSite
  :: RuntimeClaimStageBundle
  -> Either String (RuntimeSiteKey, Set.Set RuntimeClaimRevision)
pickSingletonClaimSite bundle = case
  [ pair
  | pair@(_, claims) <- Map.toAscList (runtimeClaimStageReverse bundle)
  , Set.size claims == 1
  ] of
  pair : _ -> Right pair
  [] -> Left "no singly-claimed runtime site available"

pickOne :: String -> Set.Set a -> Either String a
pickOne label values = case Set.minView values of
  Nothing -> Left ("no " <> label <> " available")
  Just (value, _) -> Right value

pickMapEntry :: String -> Map.Map k v -> Either String (k, v)
pickMapEntry label values = case Map.minViewWithKey values of
  Nothing -> Left ("no " <> label <> " available")
  Just (entry, _) -> Right entry

rebuild
  :: RuntimeClaimStageBundle
  -> Map.Map RuntimeSiteKey RuntimeSiteBinding
  -> Map.Map RuntimeClaimRevision RuntimeClaim
  -> Map.Map RuntimeClaimRevision RuntimeClaimBinding
  -> Map.Map RuntimeSiteKey (Set.Set RuntimeClaimRevision)
  -> Map.Map PhysicalRuntimeCostIdentity PhysicalRuntimeCost
  -> RuntimeClaimStageBundle
rebuild original = makeRuntimeClaimStageBundle (runtimeClaimStageBase original)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
