{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.NextStageRequirementWitnesses
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveHostAbiObligationRevision
  , steveHostAbiTargetPrecondition
  )
import Phil.Systems.CostAttribution
  ( verifyCostAttributionStageBundle
  )
import Phil.Systems.NextStageRequirement
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ t "SYS-019 SYS-018 upload predecessor remains valid" uploadPred
    , t "SYS-019 SYS-018 Steve predecessor remains valid" stevePred
    , t "SYS-019 upload exact next-stage requirements are accepted" uploadAccepted
    , t "SYS-019 Steve exact next-stage requirements are accepted" steveAccepted
    , t "SYS-019 upload exports one requirement per runtime primitive profile" uploadRequirementCount
    , t "SYS-019 Steve exports exactly one host ABI requirement" steveRequirementCount
    , t "SYS-019 shared frame primitive exports once while retaining both sites" frameRequirementSharesPrimitive
    , t "SYS-019 Steve exports the exact host ABI fact" steveExactFact
    , t "SYS-019 Steve requirement retains its derived-obligation provenance" steveDerivedObligation
    , t "SYS-019 runtime requirement cannot disappear at backend boundary" $ rejectUpload omitFrameRequirement
    , t "SYS-019 target ABI requirement cannot disappear at backend boundary" $ rejectSteve omitSteveRequirement
    , t "SYS-019 next-stage registry cannot invent a requirement" $ rejectUpload inventRequirement
    , t "SYS-019 requirement map key is exact" $ rejectUpload requirementMapKeyDrift
    , t "SYS-019 embedded requirement revision is exact" $ rejectUpload requirementRevisionDrift
    , t "SYS-019 next-stage requirement must retain source Systems refs" $ rejectUpload (mutateUploadFrame clearSources)
    , t "SYS-019 shared primitive requirement cannot omit one semantic site" $ rejectUpload (mutateUploadFrame omitOneRuntimeSite)
    , t "SYS-019 runtime requirement retains exact cost-charge provenance" $ rejectUpload (mutateUploadFrame omitCostCharge)
    , t "SYS-019 target requirement retains exact target-precondition provenance" $ rejectSteve (mutateSteveHost omitTargetPreconditionSource)
    , t "SYS-019 target requirement retains exact semantic-subject provenance" $ rejectSteve (mutateSteveHost omitSemanticSubject)
    , t "SYS-019 required fact cannot be empty" $ rejectUpload (mutateUploadFrame emptyFact)
    , t "SYS-019 native ABI folklore cannot replace an exact requirement" $ rejectUpload (mutateUploadFrame nativeAbiFolklore)
    , t "SYS-019 runtime ABI/signature contract cannot drift" $ rejectUpload (mutateUploadFrame runtimeFactDrift)
    , t "SYS-019 acceptance rule cannot be empty" $ rejectUpload (mutateUploadFrame emptyAcceptanceRule)
    , t "SYS-019 validity scope cannot be empty" $ rejectUpload (mutateUploadFrame emptyValidityScope)
    , t "SYS-019 next-stage stage identity is deterministic" deterministic
    ]
  if and results then pure () else exitFailure

t :: String -> Either String () -> IO Bool
t label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left e -> putStrLn ("FAIL: " <> label <> " -- " <> e) >> pure False

uploadPred, stevePred, uploadAccepted, steveAccepted :: Either String ()
uploadPred = uploadNextStageRequirementStage >>=
  mapLeft show . verifyCostAttributionStageBundle . nextStageRequirementStageBase
stevePred = steveNextStageRequirementStage >>=
  mapLeft show . verifyCostAttributionStageBundle . nextStageRequirementStageBase
uploadAccepted = uploadNextStageRequirementStage >>=
  mapLeft show . verifyNextStageRequirementStageBundle
steveAccepted = steveNextStageRequirementStage >>=
  mapLeft show . verifyNextStageRequirementStageBundle

uploadRequirementCount, steveRequirementCount :: Either String ()
uploadRequirementCount = do
  bundle <- uploadNextStageRequirementStage
  assert (Map.size (nextStageRequirementStageRequirements bundle) == 8)
    "expected exactly eight upload runtime-profile requirements"
steveRequirementCount = do
  bundle <- steveNextStageRequirementStage
  assert (Map.size (nextStageRequirementStageRequirements bundle) == 1)
    "expected exactly one Steve host-ABI requirement"

frameRequirementSharesPrimitive :: Either String ()
frameRequirementSharesPrimitive = do
  bundle <- uploadNextStageRequirementStage
  (_, requirement) <- requirementByBasis uploadFrameReceiveRequirementBasis bundle
  let runtimeSites = Set.fromList
        [ site
        | NextStageRuntimeSiteSource site <- Set.toAscList
            (nextStageRequirementSourceSystemsRefs requirement)
        ]
  assert (Set.size runtimeSites == 2)
    ("expected frame_receive requirement to retain two sites, got " <> show runtimeSites)

steveExactFact, steveDerivedObligation :: Either String ()
steveExactFact = do
  bundle <- steveNextStageRequirementStage
  (_, requirement) <- requirementByBasis steveHostAbiRequirementBasis bundle
  assert (nextStageRequirementRequiredFactOrContract requirement == steveHostAbiTargetPrecondition)
    "Steve next-stage fact drifted from exact Systems target precondition"
steveDerivedObligation = do
  bundle <- steveNextStageRequirementStage
  (_, requirement) <- requirementByBasis steveHostAbiRequirementBasis bundle
  assert (Set.member
      (NextStageDerivedObligationSource steveHostAbiObligationRevision)
      (nextStageRequirementSourceSystemsRefs requirement))
    "Steve host ABI requirement lost derived-obligation provenance"

rejectUpload
  :: (NextStageRequirementStageBundle -> NextStageRequirementStageBundle)
  -> Either String ()
rejectUpload mutate = do
  bundle <- uploadNextStageRequirementStage
  rejectBundle (mutate bundle)

rejectSteve
  :: (NextStageRequirementStageBundle -> NextStageRequirementStageBundle)
  -> Either String ()
rejectSteve mutate = do
  bundle <- steveNextStageRequirementStage
  rejectBundle (mutate bundle)

rejectBundle :: NextStageRequirementStageBundle -> Either String ()
rejectBundle bundle =
  case verifyNextStageRequirementStageBundle (reseal bundle) of
    Left _ -> Right ()
    Right () -> Left "mutation was accepted"

omitFrameRequirement :: NextStageRequirementStageBundle -> NextStageRequirementStageBundle
omitFrameRequirement bundle = case requirementByBasis uploadFrameReceiveRequirementBasis bundle of
  Left _ -> bundle
  Right (revision, _) -> bundle
    { nextStageRequirementStageRequirements =
        Map.delete revision (nextStageRequirementStageRequirements bundle)
    }

omitSteveRequirement :: NextStageRequirementStageBundle -> NextStageRequirementStageBundle
omitSteveRequirement bundle = case requirementByBasis steveHostAbiRequirementBasis bundle of
  Left _ -> bundle
  Right (revision, _) -> bundle
    { nextStageRequirementStageRequirements =
        Map.delete revision (nextStageRequirementStageRequirements bundle)
    }

inventRequirement :: NextStageRequirementStageBundle -> NextStageRequirementStageBundle
inventRequirement bundle = case Map.lookupMin (nextStageRequirementStageRequirements bundle) of
  Nothing -> bundle
  Just (_, requirement) ->
    let inventedRevision = NextStageRequirementRevision "invented.next-stage.requirement"
        invented = requirement
          { nextStageRequirementRevision = inventedRevision
          , nextStageRequirementBasis = NextStageRuntimePrimitiveBasis
              (RuntimePrimitiveProfileRef "invented.runtime.profile")
          }
    in bundle
      { nextStageRequirementStageRequirements = Map.insert inventedRevision invented
          (nextStageRequirementStageRequirements bundle)
      }

requirementMapKeyDrift :: NextStageRequirementStageBundle -> NextStageRequirementStageBundle
requirementMapKeyDrift bundle = case Map.lookupMin (nextStageRequirementStageRequirements bundle) of
  Nothing -> bundle
  Just (revision, requirement) ->
    let drift = NextStageRequirementRevision "drifted.map.key"
        requirements = Map.delete revision (nextStageRequirementStageRequirements bundle)
    in bundle
      { nextStageRequirementStageRequirements = Map.insert drift requirement requirements }

requirementRevisionDrift :: NextStageRequirementStageBundle -> NextStageRequirementStageBundle
requirementRevisionDrift bundle = case Map.lookupMin (nextStageRequirementStageRequirements bundle) of
  Nothing -> bundle
  Just (revision, requirement) -> bundle
    { nextStageRequirementStageRequirements = Map.insert revision
        (requirement { nextStageRequirementRevision = NextStageRequirementRevision "drifted.embedded.revision" })
        (nextStageRequirementStageRequirements bundle)
    }

mutateUploadFrame
  :: (NextStageRequirement -> NextStageRequirement)
  -> NextStageRequirementStageBundle
  -> NextStageRequirementStageBundle
mutateUploadFrame = mutateRequirement uploadFrameReceiveRequirementBasis

mutateSteveHost
  :: (NextStageRequirement -> NextStageRequirement)
  -> NextStageRequirementStageBundle
  -> NextStageRequirementStageBundle
mutateSteveHost = mutateRequirement steveHostAbiRequirementBasis

mutateRequirement
  :: NextStageRequirementBasis
  -> (NextStageRequirement -> NextStageRequirement)
  -> NextStageRequirementStageBundle
  -> NextStageRequirementStageBundle
mutateRequirement basis f bundle = case requirementByBasis basis bundle of
  Left _ -> bundle
  Right (revision, requirement) -> bundle
    { nextStageRequirementStageRequirements = Map.insert revision (f requirement)
        (nextStageRequirementStageRequirements bundle)
    }

clearSources :: NextStageRequirement -> NextStageRequirement
clearSources requirement = requirement
  { nextStageRequirementSourceSystemsRefs = Set.empty }

omitOneRuntimeSite :: NextStageRequirement -> NextStageRequirement
omitOneRuntimeSite requirement = requirement
  { nextStageRequirementSourceSystemsRefs = Set.delete siteRef refs }
  where
    refs = nextStageRequirementSourceSystemsRefs requirement
    siteRef = head
      [ ref | ref@(NextStageRuntimeSiteSource _) <- Set.toAscList refs ]

omitCostCharge :: NextStageRequirement -> NextStageRequirement
omitCostCharge requirement = requirement
  { nextStageRequirementSourceSystemsRefs = Set.filter notCost refs }
  where
    refs = nextStageRequirementSourceSystemsRefs requirement
    notCost (NextStageCostChargeSource _) = False
    notCost _ = True

omitTargetPreconditionSource :: NextStageRequirement -> NextStageRequirement
omitTargetPreconditionSource requirement = requirement
  { nextStageRequirementSourceSystemsRefs = Set.filter notTarget refs }
  where
    refs = nextStageRequirementSourceSystemsRefs requirement
    notTarget (NextStageTargetPreconditionSource _) = False
    notTarget _ = True

omitSemanticSubject :: NextStageRequirement -> NextStageRequirement
omitSemanticSubject requirement = requirement
  { nextStageRequirementSourceSystemsRefs = Set.filter notSubject refs }
  where
    refs = nextStageRequirementSourceSystemsRefs requirement
    notSubject (NextStageSemanticSubjectSource _) = False
    notSubject _ = True

emptyFact, nativeAbiFolklore, runtimeFactDrift :: NextStageRequirement -> NextStageRequirement
emptyFact requirement = requirement
  { nextStageRequirementRequiredFactOrContract = "" }
nativeAbiFolklore requirement = requirement
  { nextStageRequirementRequiredFactOrContract = "native ABI" }
runtimeFactDrift requirement = requirement
  { nextStageRequirementRequiredFactOrContract =
      "backend may infer whatever platform ABI is convenient" }

emptyAcceptanceRule :: NextStageRequirement -> NextStageRequirement
emptyAcceptanceRule requirement = requirement
  { nextStageRequirementAcceptanceRule = "" }

emptyValidityScope :: NextStageRequirement -> NextStageRequirement
emptyValidityScope requirement = requirement
  { nextStageRequirementValidityScope = NextStageValidityScope "" }

deterministic :: Either String ()
deterministic = do
  bundle <- uploadNextStageRequirementStage
  let rebuilt = makeNextStageRequirementStageBundle
        (nextStageRequirementStageBase bundle)
        (reverseMap (nextStageRequirementStageRequirements bundle))
  assert (nextStageRequirementStageRevision bundle == nextStageRequirementStageRevision rebuilt)
    "stage revision changed under requirement-map reordering"
  mapLeft show (verifyNextStageRequirementStageBundle rebuilt)

reverseMap :: Ord k => Map.Map k v -> Map.Map k v
reverseMap = Map.fromList . reverse . Map.toAscList

requirementByBasis
  :: NextStageRequirementBasis
  -> NextStageRequirementStageBundle
  -> Either String (NextStageRequirementRevision, NextStageRequirement)
requirementByBasis basis bundle = case
  [ pair
  | pair@(_, requirement) <- Map.toAscList
      (nextStageRequirementStageRequirements bundle)
  , nextStageRequirementBasis requirement == basis
  ] of
  [pair] -> Right pair
  [] -> Left ("next-stage requirement missing for basis: " <> show basis)
  many -> Left ("next-stage requirement basis is not unique: " <> show many)

reseal :: NextStageRequirementStageBundle -> NextStageRequirementStageBundle
reseal bundle = bundle
  { nextStageRequirementStageRevision =
      deriveNextStageRequirementStageRevision bundle }

assert :: Bool -> String -> Either String ()
assert ok message = if ok then Right () else Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
