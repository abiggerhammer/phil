{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.ProviderQualification (ProviderOperationKey (..))
import Phil.Examples.Phase1.ProviderCallWitnesses
  ( steveProviderCallExpectations
  , steveProviderCallStageBundle
  )
import Phil.Systems.Phase1Stage (SystemsMechanismKey (..))
import Phil.Systems.ProviderCallCorrespondence
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "REVIEW-R13 exact Steve provider-call expectations accept"
        exactSteveExpectationsAccept
    , test "REVIEW-R13 different genuinely qualified provider operation rejects"
        crossProviderDonorRejects
    , test "REVIEW-R13 different genuinely qualified same-provider operation rejects"
        sameProviderDonorRejects
    , test "REVIEW-R13 runtime symbol rename remains nonauthoritative"
        symbolRenameStillAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactSteveExpectationsAccept :: Either String ()
exactSteveExpectationsAccept = do
  bundle <- steveProviderCallStageBundle
  mapLeft show $ verifyProviderCallStageBundleAgainst steveProviderCallExpectations bundle

crossProviderDonorRejects :: Either String ()
crossProviderDonorRejects = do
  bundle <- steveProviderCallStageBundle
  compute <- requireLink digestComputeSite bundle
  donor <- requireLink blobReadSite bundle
  let bad = compute { providerCallBindingBasis = providerCallBindingBasis donor }
      mutated = replaceLink bundle digestComputeSite bad
  mapLeft show $ verifyProviderCallStageBundle mutated
  case verifyProviderCallStageBundleAgainst steveProviderCallExpectations mutated of
    Left (ProviderCallExpectedOccurrenceMismatch site expected actual) -> do
      assert (site == digestComputeSite) "wrong site in expected-occurrence rejection"
      assert (expected == "steve.digest-provider") "wrong expected provider occurrence"
      assert (actual == "steve.blob-provider") "wrong donor provider occurrence"
    other -> Left ("wrong qualified donor provider operation was accepted: " <> show other)

sameProviderDonorRejects :: Either String ()
sameProviderDonorRejects = do
  bundle <- steveProviderCallStageBundle
  compute <- requireLink digestComputeSite bundle
  donor <- requireLink digestCheckSite bundle
  let bad = compute { providerCallBindingBasis = providerCallBindingBasis donor }
      mutated = replaceLink bundle digestComputeSite bad
  mapLeft show $ verifyProviderCallStageBundle mutated
  case verifyProviderCallStageBundleAgainst steveProviderCallExpectations mutated of
    Left (ProviderCallExpectedOperationMismatch site expected actual) -> do
      assert (site == digestComputeSite) "wrong site in expected-operation rejection"
      assert (expected == ProviderOperationKey "digest.compute") "wrong expected operation"
      assert (actual == ProviderOperationKey "digest.check") "wrong donor operation"
    other -> Left ("wrong qualified same-provider operation was accepted: " <> show other)

symbolRenameStillAccepts :: Either String ()
symbolRenameStillAccepts = do
  bundle <- steveProviderCallStageBundle
  compute <- requireLink digestComputeSite bundle
  let renamed = compute { providerCallRuntimeSymbol = "renamed_backend_symbol" }
      mutated = replaceLink bundle digestComputeSite renamed
  mapLeft show $ verifyProviderCallStageBundleAgainst steveProviderCallExpectations mutated

replaceLink
  :: ProviderCallStageBundle
  -> SystemsMechanismKey
  -> ProviderCallLink
  -> ProviderCallStageBundle
replaceLink bundle key link = makeProviderCallStageBundle
  (providerCallStageBase bundle)
  (providerCallStageSelections bundle)
  (providerCallStageCallSites bundle)
  (Map.insert key link (providerCallStageLinks bundle))

requireLink
  :: SystemsMechanismKey
  -> ProviderCallStageBundle
  -> Either String ProviderCallLink
requireLink key bundle = maybe
  (Left ("missing provider call link: " <> show key))
  Right
  (Map.lookup key (providerCallStageLinks bundle))

digestComputeSite, blobReadSite, digestCheckSite :: SystemsMechanismKey
digestComputeSite = SystemsMechanismKey
  "StevePut:put.entry:term.runtime-choice.DigestProvider.compute"
blobReadSite = SystemsMechanismKey
  "SteveGet:get.entry:term.runtime-choice.BlobProvider.read"
digestCheckSite = SystemsMechanismKey
  "SteveGet:get.check:term.runtime-choice.DigestProvider.check"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
