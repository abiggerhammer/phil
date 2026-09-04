{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.CostAttributionWitnesses
import Phil.Examples.Phase1.RuntimeClaimWitnesses (uploadCompositeClaimRevision)
import Phil.Examples.Phase1.StagingEffectWitnesses (uploadDigestStagingRequirementKey)
import Phil.Systems.CostAttribution
import Phil.Systems.IR (CostClass (..), CostShape (..), DecisionId (..))
import Phil.Systems.RuntimePrimitiveReuse (RuntimePrimitiveProfileRef (..))
import Phil.Systems.StagingEffect (StagingCostIdentity (..), verifyStagingEffectStageBundle)
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ t "SYS-018 SYS-017 upload predecessor remains valid" uploadPred
    , t "SYS-018 SYS-017 Steve predecessor remains valid" stevePred
    , t "SYS-018 upload exact cost graph is accepted" uploadAccepted
    , t "SYS-018 Steve empty cost graph is accepted" steveAccepted
    , t "SYS-018 runtime basis covers selected profiles" basisCoverage
    , t "SYS-018 every runtime site retains one contribution" siteCoverage
    , t "SYS-018 every staging event retains one contribution" stagingCoverage
    , t "SYS-018 frame reuse retains two contributions" frameContributionsDistinct
    , t "SYS-018 compatible frame contributions charge once" frameChargedOnce
    , t "SYS-018 aggregate retains contribution lineage" frameLineage
    , t "SYS-018 claim multiplicity does not duplicate charges" claimsDoNotOwnCharges
    , t "SYS-018 composite claim keeps receive and digest charges" compositeCharges
    , t "SYS-018 staging cost remains TargetRequired" stagingTargetRequired
    , t "SYS-018 aggregation is exercised" aggregationPresent
    , t "SYS-018 runtime basis omission rejects" $ reject basisOmission
    , t "SYS-018 runtime basis alias rejects" $ reject basisAlias
    , t "SYS-018 runtime basis key drift rejects" $ reject basisKeyDrift
    , t "SYS-018 unknown lowering decision rejects" $ reject unknownDecision
    , t "SYS-018 empty final charge identity rejects" $ reject emptyCharge
    , t "SYS-018 empty-shape lowering decision rejects" $ reject emptyShapeDecision
    , t "SYS-018 incompatible cost classes cannot aggregate" incompatibleClass
    , t "SYS-018 incompatible cost shapes cannot aggregate" incompatibleShape
    , t "SYS-018 contribution omission rejects" $ reject contributionOmission
    , t "SYS-018 invented contribution rejects" $ reject contributionInvented
    , t "SYS-018 contribution key drift rejects" $ reject contributionKeyDrift
    , t "SYS-018 contribution class tamper rejects" $ reject contributionClassTamper
    , t "SYS-018 contribution shape tamper rejects" $ reject contributionShapeTamper
    , t "SYS-018 contribution claim tamper rejects" $ reject contributionClaimTamper
    , t "SYS-018 contribution-charge omission rejects" $ reject contributionChargeOmission
    , t "SYS-018 contribution-charge retarget rejects" $ reject contributionChargeRetarget
    , t "SYS-018 final charge omission rejects" $ reject chargeOmission
    , t "SYS-018 invented final charge rejects" $ reject chargeInvented
    , t "SYS-018 final charge identity drift rejects" $ reject chargeKeyDrift
    , t "SYS-018 final charge contribution tamper rejects" $ reject chargeContributionTamper
    , t "SYS-018 final charge claim tamper rejects" $ reject chargeClaimTamper
    , t "SYS-018 runtime-site reverse relation rejects omission" $ reject siteReverseOmission
    , t "SYS-018 runtime-site reverse relation rejects retarget" $ reject siteReverseRetarget
    , t "SYS-018 claim-charge relation rejects omission" $ reject claimReverseOmission
    , t "SYS-018 claim-charge relation rejects invented charge" $ reject claimReverseInvented
    , t "SYS-018 staging reverse relation rejects omission" $ reject stagingReverseOmission
    , t "SYS-018 staging reverse relation rejects retarget" $ reject stagingReverseRetarget
    , t "SYS-018 cost-attribution identity is deterministic" deterministic
    ]
  if and results then pure () else exitFailure

t :: String -> Either String () -> IO Bool
t label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left e -> putStrLn ("FAIL: " <> label <> " -- " <> e) >> pure False

uploadPred, stevePred, uploadAccepted, steveAccepted :: Either String ()
uploadPred = uploadCostAttributionStage >>= mapLeft show . verifyStagingEffectStageBundle . costAttributionStageBase
stevePred = steveCostAttributionStage >>= mapLeft show . verifyStagingEffectStageBundle . costAttributionStageBase
uploadAccepted = uploadCostAttributionStage >>= mapLeft show . verifyCostAttributionStageBundle
steveAccepted = do
  b <- steveCostAttributionStage
  assert (Map.null (costAttributionStageRuntimeBases b)) "Steve runtime bases nonempty"
  assert (Map.null (costAttributionStageContributions b)) "Steve contributions nonempty"
  assert (Map.null (costAttributionStageContributionCharges b)) "Steve contribution-charge relation nonempty"
  assert (Map.null (costAttributionStageCharges b)) "Steve charges nonempty"
  assert (Map.null (costAttributionStageRuntimeSiteContributions b)) "Steve site relation nonempty"
  assert (Map.null (costAttributionStageClaimCharges b)) "Steve claim relation nonempty"
  assert (Map.null (costAttributionStageStagingContributions b)) "Steve staging relation nonempty"
  mapLeft show (verifyCostAttributionStageBundle b)

basisCoverage, siteCoverage, stagingCoverage :: Either String ()
basisCoverage = do
  b <- uploadCostAttributionStage
  let used = Set.fromList [p | c <- Map.elems (costAttributionStageContributions b), RuntimeSiteCostMechanism _ p _ <- [costContributionMechanism c]]
  assert (used == Map.keysSet (costAttributionStageRuntimeBases b)) "runtime profile basis is not exact"
siteCoverage = do
  b <- uploadCostAttributionStage
  assert (deriveRuntimeSiteContributions (costAttributionStageContributions b) == costAttributionStageRuntimeSiteContributions b) "runtime site relation mismatch"
stagingCoverage = do
  b <- uploadCostAttributionStage
  assert (deriveStagingContributions (costAttributionStageContributions b) == costAttributionStageStagingContributions b) "staging relation mismatch"

frameContributionsDistinct, frameChargedOnce, frameLineage :: Either String ()
frameContributionsDistinct = uploadCostAttributionStage >>= \b -> frameIds b >>= \ids -> assert (Set.size ids == 2) (show ids)
frameChargedOnce = do
  b <- uploadCostAttributionStage
  ids <- frameIds b
  let charges = Set.fromList [c | i <- Set.toAscList ids, Just c <- [Map.lookup i (costAttributionStageContributionCharges b)]]
  assert (charges == Set.singleton uploadFrameReceiveChargeIdentity) (show charges)
frameLineage = do
  b <- uploadCostAttributionStage
  ids <- frameIds b
  charge <- need "frame charge" $ Map.lookup uploadFrameReceiveChargeIdentity (costAttributionStageCharges b)
  assert (attributedCostContributions charge == ids) "frame contribution lineage collapsed"

claimsDoNotOwnCharges, compositeCharges, stagingTargetRequired, aggregationPresent :: Either String ()
claimsDoNotOwnCharges = do
  b <- uploadCostAttributionStage
  let refs = sum (map Set.size (Map.elems (costAttributionStageClaimCharges b)))
  assert (refs > Map.size (costAttributionStageCharges b)) "claims appear to own duplicate charges"
compositeCharges = do
  b <- uploadCostAttributionStage
  cs <- need "composite claim charges" $ Map.lookup uploadCompositeClaimRevision (costAttributionStageClaimCharges b)
  assert (cs == Set.fromList [CostChargeIdentity "cost.runtime.receive_exact.v1", CostChargeIdentity "cost.runtime.digest.v1"]) (show cs)
stagingTargetRequired = do
  b <- uploadCostAttributionStage
  ci <- need "staging contribution" $ Map.lookup uploadDigestStagingRequirementKey (costAttributionStageStagingContributions b)
  chargeId <- need "staging charge" $ Map.lookup ci (costAttributionStageContributionCharges b)
  charge <- need "staging charge entry" $ Map.lookup chargeId (costAttributionStageCharges b)
  assert (attributedCostClass charge == TargetRequired) "staging charge is not TargetRequired"
aggregationPresent = do
  b <- uploadCostAttributionStage
  assert (Map.size (costAttributionStageContributions b) == 10 && Map.size (costAttributionStageCharges b) == 9) "expected 10 contributions -> 9 charges"

reject :: (CostAttributionStageBundle -> CostAttributionStageBundle) -> Either String ()
reject mutate = do
  b <- uploadCostAttributionStage
  case verifyCostAttributionStageBundle (reseal (mutate b)) of
    Left _ -> Right ()
    Right () -> Left "mutation was accepted"

basisOmission, basisAlias, basisKeyDrift, unknownDecision, emptyCharge, emptyShapeDecision :: CostAttributionStageBundle -> CostAttributionStageBundle
basisOmission b = let (k,_) = Map.findMin (costAttributionStageRuntimeBases b) in b { costAttributionStageRuntimeBases = Map.delete k (costAttributionStageRuntimeBases b) }
basisAlias b = let (_,v) = Map.findMin (costAttributionStageRuntimeBases b); k = RuntimePrimitiveProfileRef "invented.profile" in b { costAttributionStageRuntimeBases = Map.insert k v (costAttributionStageRuntimeBases b) }
basisKeyDrift b = let (k,v) = Map.findMin (costAttributionStageRuntimeBases b); bad = v { runtimeCostBasisProfile = RuntimePrimitiveProfileRef "wrong.profile" } in b { costAttributionStageRuntimeBases = Map.insert k bad (costAttributionStageRuntimeBases b) }
unknownDecision b = let (k,v) = Map.findMin (costAttributionStageRuntimeBases b); bad = v { runtimeCostBasisDecision = DecisionId "missing.decision" } in b { costAttributionStageRuntimeBases = Map.insert k bad (costAttributionStageRuntimeBases b) }
emptyCharge b = let (k,v) = Map.findMin (costAttributionStageRuntimeBases b); bad = v { runtimeCostBasisCharge = CostChargeIdentity "" } in b { costAttributionStageRuntimeBases = Map.insert k bad (costAttributionStageRuntimeBases b) }
emptyShapeDecision b = let (k,v) = Map.findMin (costAttributionStageRuntimeBases b); bad = v { runtimeCostBasisDecision = DecisionId "lower.erase.pending_wrapper" } in b { costAttributionStageRuntimeBases = Map.insert k bad (costAttributionStageRuntimeBases b) }

incompatibleClass, incompatibleShape :: Either String ()
incompatibleClass = incompatibleAggregation changeClass isClass
  where
    changeClass contribution = contribution
      { costContributionClass = differentCostClass (costContributionClass contribution) }
    isClass (Left (CostChargeIncompatibleClass _ xs)) = Set.size xs > 1
    isClass _ = False

incompatibleShape = incompatibleAggregation changeShape isShape
  where
    changeShape contribution = contribution
      { costContributionShape =
          (costContributionShape contribution)
            { costFrequency = Just "incompatible-test-frequency" }
      }
    isShape (Left (CostChargeIncompatibleShape _ xs)) = Set.size xs > 1
    isShape _ = False

incompatibleAggregation
  :: (CostContribution -> CostContribution)
  -> (Either CostAttributionVerificationError (Map.Map CostChargeIdentity AttributedCost) -> Bool)
  -> Either String ()
incompatibleAggregation mutate accept = do
  b <- uploadCostAttributionStage
  case
    [ pair
    | pair@(_, contribution) <- Map.toAscList (costAttributionStageContributions b)
    , RuntimeSiteCostMechanism {} <- [costContributionMechanism contribution]
    ] of
      (leftId, left) : (rightId, right) : _ -> do
        let sharedCharge = CostChargeIdentity "cost.test.incompatible-aggregation"
            contributions = Map.fromList
              [ (leftId, left)
              , (rightId, mutate right)
              ]
            mapping = Map.fromList
              [ (leftId, sharedCharge)
              , (rightId, sharedCharge)
              ]
            result = deriveAttributedCosts contributions mapping
        if accept result
          then Right ()
          else Left ("incompatible aggregation produced wrong result: " <> show result)
      _ -> Left "need at least two runtime cost contributions"

differentCostClass :: CostClass -> CostClass
differentCostClass SemanticRequired = DefensiveProfile
differentCostClass _ = SemanticRequired

contributionOmission, contributionInvented, contributionKeyDrift, contributionClassTamper, contributionShapeTamper, contributionClaimTamper :: CostAttributionStageBundle -> CostAttributionStageBundle
contributionOmission b = let (k,_) = Map.findMin (costAttributionStageContributions b) in b { costAttributionStageContributions = Map.delete k (costAttributionStageContributions b) }
contributionInvented b = let (_,v) = Map.findMin (costAttributionStageContributions b); k = StagingCostContribution (StagingCostIdentity "invented"); bad = v { costContributionIdentity = k } in b { costAttributionStageContributions = Map.insert k bad (costAttributionStageContributions b) }
contributionKeyDrift b = let (k,v) = firstRuntimeContribution b; bad = v { costContributionIdentity = StagingCostContribution (StagingCostIdentity "drift") } in b { costAttributionStageContributions = Map.insert k bad (costAttributionStageContributions b) }
contributionClassTamper b = let (k,v) = firstRuntimeContribution b; bad = v { costContributionClass = DefensiveProfile } in b { costAttributionStageContributions = Map.insert k bad (costAttributionStageContributions b) }
contributionShapeTamper b = let (k,v) = firstRuntimeContribution b; s = costContributionShape v; bad = v { costContributionShape = s { costFrequency = Just "tampered" } } in b { costAttributionStageContributions = Map.insert k bad (costAttributionStageContributions b) }
contributionClaimTamper b = let (k,v) = firstRuntimeContribution b; bad = v { costContributionRuntimeClaims = Set.empty } in b { costAttributionStageContributions = Map.insert k bad (costAttributionStageContributions b) }

contributionChargeOmission, contributionChargeRetarget :: CostAttributionStageBundle -> CostAttributionStageBundle
contributionChargeOmission b = let (k,_) = Map.findMin (costAttributionStageContributionCharges b) in b { costAttributionStageContributionCharges = Map.delete k (costAttributionStageContributionCharges b) }
contributionChargeRetarget b = let xs = Map.toAscList (costAttributionStageContributionCharges b); (k,old) = head xs; replacement = head [v | (_,v) <- tail xs, v /= old] in b { costAttributionStageContributionCharges = Map.insert k replacement (costAttributionStageContributionCharges b) }

chargeOmission, chargeInvented, chargeKeyDrift, chargeContributionTamper, chargeClaimTamper :: CostAttributionStageBundle -> CostAttributionStageBundle
chargeOmission b = let (k,_) = Map.findMin (costAttributionStageCharges b) in b { costAttributionStageCharges = Map.delete k (costAttributionStageCharges b) }
chargeInvented b = let (_,v) = Map.findMin (costAttributionStageCharges b); k = CostChargeIdentity "invented.charge"; bad = v { attributedCostIdentity = k } in b { costAttributionStageCharges = Map.insert k bad (costAttributionStageCharges b) }
chargeKeyDrift b = let (k,v) = Map.findMin (costAttributionStageCharges b); bad = v { attributedCostIdentity = CostChargeIdentity "drift.charge" } in b { costAttributionStageCharges = Map.insert k bad (costAttributionStageCharges b) }
chargeContributionTamper b = let (k,v) = Map.findMin (costAttributionStageCharges b); bad = v { attributedCostContributions = Set.empty } in b { costAttributionStageCharges = Map.insert k bad (costAttributionStageCharges b) }
chargeClaimTamper b = let (k,v) = firstRuntimeCharge b; bad = v { attributedCostRuntimeClaims = Set.empty } in b { costAttributionStageCharges = Map.insert k bad (costAttributionStageCharges b) }

siteReverseOmission, siteReverseRetarget, claimReverseOmission, claimReverseInvented, stagingReverseOmission, stagingReverseRetarget :: CostAttributionStageBundle -> CostAttributionStageBundle
siteReverseOmission b = let (k,_) = Map.findMin (costAttributionStageRuntimeSiteContributions b) in b { costAttributionStageRuntimeSiteContributions = Map.delete k (costAttributionStageRuntimeSiteContributions b) }
siteReverseRetarget b = let xs = Map.toAscList (costAttributionStageRuntimeSiteContributions b); (k,old) = head xs; replacement = head [v | (_,v) <- tail xs, v /= old] in b { costAttributionStageRuntimeSiteContributions = Map.insert k replacement (costAttributionStageRuntimeSiteContributions b) }
claimReverseOmission b = let (k,cs) = Map.findMin (costAttributionStageClaimCharges b); c = Set.findMin cs in b { costAttributionStageClaimCharges = Map.insert k (Set.delete c cs) (costAttributionStageClaimCharges b) }
claimReverseInvented b = let (k,cs) = Map.findMin (costAttributionStageClaimCharges b) in b { costAttributionStageClaimCharges = Map.insert k (Set.insert (CostChargeIdentity "invented.claim.charge") cs) (costAttributionStageClaimCharges b) }
stagingReverseOmission b = b { costAttributionStageStagingContributions = Map.delete uploadDigestStagingRequirementKey (costAttributionStageStagingContributions b) }
stagingReverseRetarget b = let (runtimeId,_) = firstRuntimeContribution b in b { costAttributionStageStagingContributions = Map.insert uploadDigestStagingRequirementKey runtimeId (costAttributionStageStagingContributions b) }

deterministic :: Either String ()
deterministic = do
  b <- uploadCostAttributionStage
  let rebuilt = makeCostAttributionStageBundle (costAttributionStageBase b)
        (reverseMap (costAttributionStageRuntimeBases b)) (reverseMap (costAttributionStageContributions b))
        (reverseMap (costAttributionStageContributionCharges b)) (reverseMap (costAttributionStageCharges b))
        (reverseMap (costAttributionStageRuntimeSiteContributions b)) (reverseMap (costAttributionStageClaimCharges b))
        (reverseMap (costAttributionStageStagingContributions b))
  assert (costAttributionStageRevision b == costAttributionStageRevision rebuilt) "revision changed under map reorder"
  mapLeft show (verifyCostAttributionStageBundle rebuilt)

reverseMap :: Ord k => Map.Map k v -> Map.Map k v
reverseMap = Map.fromList . reverse . Map.toAscList

frameIds :: CostAttributionStageBundle -> Either String (Set.Set CostContributionIdentity)
frameIds b = let p = RuntimePrimitiveProfileRef "upload.runtime.frame_receive"; ids = Set.fromList [i | (i,c) <- Map.toAscList (costAttributionStageContributions b), RuntimeSiteCostMechanism _ q _ <- [costContributionMechanism c], p == q] in if Set.null ids then Left "frame contributions missing" else Right ids

firstRuntimeContribution :: CostAttributionStageBundle -> (CostContributionIdentity, CostContribution)
firstRuntimeContribution b = head [x | x@(_,c) <- Map.toAscList (costAttributionStageContributions b), RuntimeSiteCostMechanism _ _ _ <- [costContributionMechanism c]]

firstRuntimeCharge :: CostAttributionStageBundle -> (CostChargeIdentity, AttributedCost)
firstRuntimeCharge b = head [x | x@(_,c) <- Map.toAscList (costAttributionStageCharges b), not (Set.null (attributedCostRuntimeClaims c))]

reseal :: CostAttributionStageBundle -> CostAttributionStageBundle
reseal b = b { costAttributionStageRevision = deriveCostAttributionStageRevision b }

need :: String -> Maybe a -> Either String a
need label = maybe (Left (label <> " missing")) Right

assert :: Bool -> String -> Either String ()
assert ok msg = if ok then Right () else Left msg

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
