{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.RuntimeClaimWitnesses
  ( steveRuntimeClaimStage
  , uploadRuntimeClaimStage
  )
import Phil.Examples.Phase1.RuntimePrimitiveWitnesses
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeSiteKey
  , verifyRuntimeClaimStageBundle
  )
import Phil.Systems.RuntimePrimitiveReuse
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-016 SYS-015 upload predecessor remains valid" uploadRuntimeClaimRegression
    , test "SYS-016 SYS-015 Steve predecessor remains valid" steveRuntimeClaimRegression
    , test "SYS-016 upload primitive reuse relation is accepted" uploadPrimitiveReuseAccepted
    , test "SYS-016 Steve empty primitive reuse relation is accepted" stevePrimitiveReuseAccepted
    , test "SYS-016 upload reuses one frame-receive primitive across distinct sites" sharedFramePrimitivePresent
    , test "SYS-016 reused primitive retains distinct runtime-site identities" sharedSitesRemainDistinct
    , test "SYS-016 reused primitive retains distinct exact claim identities" sharedClaimsRemainDistinct
    , test "SYS-016 reused primitive retains distinct semantic subject identities" sharedSubjectsRemainDistinct
    , test "SYS-016 reused primitive retains distinct physical cost identities" sharedCostsRemainDistinct
    , test "SYS-016 primitive site cannot disappear from exact site registry" siteOmissionRejected
    , test "SYS-016 primitive profile identity cannot be empty" emptyProfileRejected
    , test "SYS-016 primitive profile cannot be silently relabeled" profileRelabelRejected
    , test "SYS-016 primitive reuse cannot collapse claim identity" claimCollapseRejected
    , test "SYS-016 primitive reuse cannot collapse semantic subject identity" subjectCollapseRejected
    , test "SYS-016 primitive reuse cannot collapse site-owned physical cost identity" costCollapseRejected
    , test "SYS-016 primitive-to-site reverse relation is exact" reverseOmissionRejected
    , test "SYS-016 reverse relation cannot invent a primitive-profile alias" reverseAliasRejected
    , test "SYS-016 primitive-reuse stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadRuntimeClaimRegression :: Either String ()
uploadRuntimeClaimRegression = do
  bundle <- uploadRuntimeClaimStage
  mapLeft show (verifyRuntimeClaimStageBundle bundle)

steveRuntimeClaimRegression :: Either String ()
steveRuntimeClaimRegression = do
  bundle <- steveRuntimeClaimStage
  mapLeft show (verifyRuntimeClaimStageBundle bundle)

uploadPrimitiveReuseAccepted :: Either String ()
uploadPrimitiveReuseAccepted = do
  bundle <- uploadRuntimePrimitiveStage
  mapLeft show (verifyRuntimePrimitiveStageBundle bundle)

stevePrimitiveReuseAccepted :: Either String ()
stevePrimitiveReuseAccepted = do
  bundle <- steveRuntimePrimitiveStage
  mapLeft show (verifyRuntimePrimitiveStageBundle bundle)

sharedFramePrimitivePresent :: Either String ()
sharedFramePrimitivePresent = do
  bundle <- uploadRuntimePrimitiveStage
  sites <- requireFrameSites bundle
  assert
    (Set.size sites >= 2)
    "frame-receive primitive profile is not reused across multiple exact sites"

sharedSitesRemainDistinct :: Either String ()
sharedSitesRemainDistinct = do
  bundle <- uploadRuntimePrimitiveStage
  (left, right) <- requireFrameSitePair bundle
  assert (left /= right) "shared primitive collapsed two runtime-site identities"

sharedClaimsRemainDistinct :: Either String ()
sharedClaimsRemainDistinct = do
  bundle <- uploadRuntimePrimitiveStage
  (left, right) <- requireFrameSitePair bundle
  leftBinding <- requireSiteBinding bundle left
  rightBinding <- requireSiteBinding bundle right
  assert
    (not (Set.null (runtimePrimitiveSiteClaims leftBinding))
      && not (Set.null (runtimePrimitiveSiteClaims rightBinding))
      && runtimePrimitiveSiteClaims leftBinding
          /= runtimePrimitiveSiteClaims rightBinding)
    "shared frame primitive collapsed exact claim identities"

sharedSubjectsRemainDistinct :: Either String ()
sharedSubjectsRemainDistinct = do
  bundle <- uploadRuntimePrimitiveStage
  (left, right) <- requireFrameSitePair bundle
  leftBinding <- requireSiteBinding bundle left
  rightBinding <- requireSiteBinding bundle right
  assert
    (not (Set.null (runtimePrimitiveSiteSubjects leftBinding))
      && not (Set.null (runtimePrimitiveSiteSubjects rightBinding))
      && runtimePrimitiveSiteSubjects leftBinding
          /= runtimePrimitiveSiteSubjects rightBinding)
    "shared frame primitive collapsed semantic subject identities"

sharedCostsRemainDistinct :: Either String ()
sharedCostsRemainDistinct = do
  bundle <- uploadRuntimePrimitiveStage
  (left, right) <- requireFrameSitePair bundle
  leftBinding <- requireSiteBinding bundle left
  rightBinding <- requireSiteBinding bundle right
  assert
    (runtimePrimitiveSiteCostIdentity leftBinding
      /= runtimePrimitiveSiteCostIdentity rightBinding)
    "shared frame primitive collapsed site-owned physical cost identities"

siteOmissionRejected :: Either String ()
siteOmissionRejected = do
  original <- uploadRuntimePrimitiveStage
  site <- fst <$> requireFrameSitePair original
  let sites = Map.delete site (runtimePrimitiveStageSites original)
      mutated = rebuild original sites (deriveRuntimePrimitiveReverse sites)
  case verifyRuntimePrimitiveStageBundle mutated of
    Left (RuntimePrimitiveSiteDomainMismatch expected actual)
      | Set.member site expected && not (Set.member site actual) -> Right ()
    other -> Left ("primitive site omission was accepted: " <> show other)

emptyProfileRejected :: Either String ()
emptyProfileRejected = do
  original <- uploadRuntimePrimitiveStage
  site <- fst <$> requireFrameSitePair original
  binding <- requireSiteBinding original site
  let bad = binding
        { runtimePrimitiveSiteProfile = RuntimePrimitiveProfileRef "" }
      sites = Map.insert site bad (runtimePrimitiveStageSites original)
      mutated = rebuild original sites (deriveRuntimePrimitiveReverse sites)
  case verifyRuntimePrimitiveStageBundle mutated of
    Left (RuntimePrimitiveEmptyProfile actual) | actual == site -> Right ()
    other -> Left ("empty primitive profile was accepted: " <> show other)

profileRelabelRejected :: Either String ()
profileRelabelRejected = do
  original <- uploadRuntimePrimitiveStage
  site <- fst <$> requireFrameSitePair original
  binding <- requireSiteBinding original site
  let invented = RuntimePrimitiveProfileRef "upload.runtime.invented-profile"
      bad = binding { runtimePrimitiveSiteProfile = invented }
      sites = Map.insert site bad (runtimePrimitiveStageSites original)
      mutated = rebuild original sites (deriveRuntimePrimitiveReverse sites)
  case verifyRuntimePrimitiveStageBundle mutated of
    Left (RuntimePrimitiveProfileMismatch actual expected observed)
      | actual == site
          && expected == uploadFrameReceivePrimitiveProfile
          && observed == invented -> Right ()
    other -> Left ("primitive profile relabel was accepted: " <> show other)

claimCollapseRejected :: Either String ()
claimCollapseRejected = do
  original <- uploadRuntimePrimitiveStage
  (left, right) <- requireFrameSitePair original
  leftBinding <- requireSiteBinding original left
  rightBinding <- requireSiteBinding original right
  let bad = rightBinding
        { runtimePrimitiveSiteClaims = runtimePrimitiveSiteClaims leftBinding }
      sites = Map.insert right bad (runtimePrimitiveStageSites original)
      mutated = rebuild original sites (runtimePrimitiveStageReverse original)
  case verifyRuntimePrimitiveStageBundle mutated of
    Left (RuntimePrimitiveClaimIdentityMismatch actual expected observed)
      | actual == right && expected /= observed -> Right ()
    other -> Left ("claim identity collapse was accepted: " <> show other)

subjectCollapseRejected :: Either String ()
subjectCollapseRejected = do
  original <- uploadRuntimePrimitiveStage
  (left, right) <- requireFrameSitePair original
  leftBinding <- requireSiteBinding original left
  rightBinding <- requireSiteBinding original right
  let bad = rightBinding
        { runtimePrimitiveSiteSubjects = runtimePrimitiveSiteSubjects leftBinding }
      sites = Map.insert right bad (runtimePrimitiveStageSites original)
      mutated = rebuild original sites (runtimePrimitiveStageReverse original)
  case verifyRuntimePrimitiveStageBundle mutated of
    Left (RuntimePrimitiveSubjectIdentityMismatch actual expected observed)
      | actual == right && expected /= observed -> Right ()
    other -> Left ("semantic subject identity collapse was accepted: " <> show other)

costCollapseRejected :: Either String ()
costCollapseRejected = do
  original <- uploadRuntimePrimitiveStage
  (left, right) <- requireFrameSitePair original
  leftBinding <- requireSiteBinding original left
  rightBinding <- requireSiteBinding original right
  let bad = rightBinding
        { runtimePrimitiveSiteCostIdentity =
            runtimePrimitiveSiteCostIdentity leftBinding }
      sites = Map.insert right bad (runtimePrimitiveStageSites original)
      mutated = rebuild original sites (runtimePrimitiveStageReverse original)
  case verifyRuntimePrimitiveStageBundle mutated of
    Left (RuntimePrimitiveSharedCostIdentityCollapse profile grouped costs)
      | profile == uploadFrameReceivePrimitiveProfile
          && Set.member left grouped
          && Set.member right grouped
          && Set.size costs < Set.size grouped -> Right ()
    other -> Left ("site-owned physical cost collapse was accepted: " <> show other)

reverseOmissionRejected :: Either String ()
reverseOmissionRejected = do
  original <- uploadRuntimePrimitiveStage
  site <- fst <$> requireFrameSitePair original
  grouped <- requireFrameSites original
  let badReverse = Map.insert uploadFrameReceivePrimitiveProfile
        (Set.delete site grouped)
        (runtimePrimitiveStageReverse original)
      mutated = rebuild original (runtimePrimitiveStageSites original) badReverse
  case verifyRuntimePrimitiveStageBundle mutated of
    Left (RuntimePrimitiveReverseSitesMismatch profile expected observed)
      | profile == uploadFrameReceivePrimitiveProfile
          && Set.member site expected
          && not (Set.member site observed) -> Right ()
    other -> Left ("primitive reverse omission was accepted: " <> show other)

reverseAliasRejected :: Either String ()
reverseAliasRejected = do
  original <- uploadRuntimePrimitiveStage
  site <- fst <$> requireFrameSitePair original
  let alias = RuntimePrimitiveProfileRef "upload.runtime.frame_receive.alias"
      badReverse = Map.insert alias (Set.singleton site)
        (runtimePrimitiveStageReverse original)
      mutated = rebuild original (runtimePrimitiveStageSites original) badReverse
  case verifyRuntimePrimitiveStageBundle mutated of
    Left (RuntimePrimitiveReverseDomainMismatch expected actual)
      | not (Set.member alias expected) && Set.member alias actual -> Right ()
    other -> Left ("invented primitive-profile alias was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- uploadRuntimePrimitiveStage
  let reverseMap value = Map.fromList (reverse (Map.toAscList value))
      rebuilt = makeRuntimePrimitiveStageBundle
        (runtimePrimitiveStageBase original)
        (reverseMap (runtimePrimitiveStageSites original))
        (reverseMap (runtimePrimitiveStageReverse original))
  assert
    (runtimePrimitiveStageRevision original
      == runtimePrimitiveStageRevision rebuilt)
    "runtime primitive-reuse revision changed with map/set enumeration order"
  mapLeft show (verifyRuntimePrimitiveStageBundle rebuilt)

requireFrameSites
  :: RuntimePrimitiveStageBundle
  -> Either String (Set.Set RuntimeSiteKey)
requireFrameSites bundle = case Map.lookup uploadFrameReceivePrimitiveProfile
    (runtimePrimitiveStageReverse bundle) of
  Nothing -> Left "upload frame-receive primitive profile missing"
  Just sites -> Right sites

requireFrameSitePair
  :: RuntimePrimitiveStageBundle
  -> Either String (RuntimeSiteKey, RuntimeSiteKey)
requireFrameSitePair bundle = do
  sites <- requireFrameSites bundle
  case Set.toAscList sites of
    left : right : _ -> Right (left, right)
    _ -> Left "fewer than two upload frame-receive sites available"

requireSiteBinding
  :: RuntimePrimitiveStageBundle
  -> RuntimeSiteKey
  -> Either String RuntimePrimitiveSiteBinding
requireSiteBinding bundle site = maybe
  (Left ("runtime primitive site missing: " <> show site))
  Right
  (Map.lookup site (runtimePrimitiveStageSites bundle))

rebuild
  :: RuntimePrimitiveStageBundle
  -> Map.Map RuntimeSiteKey RuntimePrimitiveSiteBinding
  -> Map.Map RuntimePrimitiveProfileRef (Set.Set RuntimeSiteKey)
  -> RuntimePrimitiveStageBundle
rebuild original = makeRuntimePrimitiveStageBundle
  (runtimePrimitiveStageBase original)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
