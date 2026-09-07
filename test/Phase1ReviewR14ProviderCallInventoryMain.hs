{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.AuthorityEffectWitnesses
  ( steveAuthorityEffectStageBundle )
import Phil.Examples.Phase1.ProviderCallWitnesses
  ( steveProviderCallExpectations
  , steveProviderCallStageBundle
  )
import Phil.Systems.AuthorityEffectCorrespondence
import Phil.Systems.Phase1Stage (SystemsMechanismKey (..))
import Phil.Systems.ProviderCallCorrespondence
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "REVIEW-R14 complete provider inventory accepts exact Steve stage"
        completeProviderAccepts
    , test "REVIEW-R14 relative provider validator admits coordinated site/link deletion"
        relativeProviderAllowsJointDeletion
    , test "REVIEW-R14 independent provider inventory rejects coordinated site/link deletion"
        completeProviderRejectsJointDeletion
    , test "REVIEW-R14 relative authority/effect validator admits coordinated site/link/use deletion"
        relativeAuthorityAllowsJointDeletion
    , test "REVIEW-R14 independent authority/effect inventory rejects coordinated deletion"
        completeAuthorityRejectsJointDeletion
    , test "REVIEW-R14 empty relative provider inventory is not independent completeness"
        emptyRelativeInventoryControl
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

completeProviderAccepts :: Either String ()
completeProviderAccepts = do
  bundle <- steveProviderCallStageBundle
  mapLeft show $ verifyProviderCallStageBundleCompleteAgainst
    steveProviderCallExpectations bundle

relativeProviderAllowsJointDeletion :: Either String ()
relativeProviderAllowsJointDeletion = do
  bundle <- steveProviderCallStageBundle
  mapLeft show $ verifyProviderCallStageBundle (dropProviderSite digestComputeSite bundle)

completeProviderRejectsJointDeletion :: Either String ()
completeProviderRejectsJointDeletion = do
  bundle <- steveProviderCallStageBundle
  let mutated = dropProviderSite digestComputeSite bundle
      expectedDomain = Map.keysSet steveProviderCallExpectations
      actualDomain = providerCallStageCallSites mutated
  case verifyProviderCallStageBundleCompleteAgainst steveProviderCallExpectations mutated of
    Left (ProviderCallRequiredSiteDomainMismatch expected actual) -> do
      assert (expected == expectedDomain) "wrong independent required-site domain"
      assert (actual == actualDomain) "wrong candidate provider-call domain"
      assert (Set.member digestComputeSite expected) "fixture lost required digest-compute site"
      assert (Set.notMember digestComputeSite actual) "fixture did not delete candidate digest-compute site"
    other -> Left ("coordinated provider site/link deletion was not rejected: " <> show other)

relativeAuthorityAllowsJointDeletion :: Either String ()
relativeAuthorityAllowsJointDeletion = do
  bundle <- steveAuthorityEffectStageBundle
  mapLeft show $ verifyAuthorityEffectStageBundle (dropAuthoritySite digestComputeSite bundle)

completeAuthorityRejectsJointDeletion :: Either String ()
completeAuthorityRejectsJointDeletion = do
  bundle <- steveAuthorityEffectStageBundle
  let mutated = dropAuthoritySite digestComputeSite bundle
      expectedDomain = Map.keysSet steveProviderCallExpectations
      actualDomain = providerCallStageCallSites (authorityEffectStageBase mutated)
  case verifyAuthorityEffectStageBundleAgainst steveProviderCallExpectations mutated of
    Left (AuthorityEffectBaseStageError
      (ProviderCallRequiredSiteDomainMismatch expected actual)) -> do
        assert (expected == expectedDomain) "wrong authority-stage required-site domain"
        assert (actual == actualDomain) "wrong authority-stage candidate domain"
    other -> Left ("coordinated site/link/use deletion escaped independent authority gate: " <> show other)

emptyRelativeInventoryControl :: Either String ()
emptyRelativeInventoryControl = do
  bundle <- steveProviderCallStageBundle
  let emptyCandidate = makeProviderCallStageBundle
        (providerCallStageBase bundle)
        (providerCallStageSelections bundle)
        Set.empty
        Map.empty
  mapLeft show $ verifyProviderCallStageBundle emptyCandidate
  case verifyProviderCallStageBundleCompleteAgainst steveProviderCallExpectations emptyCandidate of
    Left (ProviderCallRequiredSiteDomainMismatch expected actual) -> do
      assert (expected == Map.keysSet steveProviderCallExpectations)
        "empty candidate changed independent required inventory"
      assert (Set.null actual) "empty candidate unexpectedly retained provider-call sites"
    other -> Left ("empty candidate was treated as independently complete: " <> show other)

dropProviderSite
  :: SystemsMechanismKey
  -> ProviderCallStageBundle
  -> ProviderCallStageBundle
dropProviderSite site bundle = makeProviderCallStageBundle
  (providerCallStageBase bundle)
  (providerCallStageSelections bundle)
  (Set.delete site (providerCallStageCallSites bundle))
  (Map.delete site (providerCallStageLinks bundle))

dropAuthoritySite
  :: SystemsMechanismKey
  -> AuthorityEffectStageBundle
  -> AuthorityEffectStageBundle
dropAuthoritySite site bundle = makeAuthorityEffectStageBundle
  (dropProviderSite site (authorityEffectStageBase bundle))
  (authorityEffectStageSurfaces bundle)
  (Map.delete site (authorityEffectStageUses bundle))

digestComputeSite :: SystemsMechanismKey
digestComputeSite = SystemsMechanismKey
  "StevePut:put.entry:term.runtime-choice.DigestProvider.compute"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
