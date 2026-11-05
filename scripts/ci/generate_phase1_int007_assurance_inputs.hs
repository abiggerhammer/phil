{-# LANGUAGE OverloadedStrings #-}

-- Generate exact INT-007 assurance inputs from the authoritative fixtures.
-- This program intentionally never derives digests from stale TSV contents.
module Main (main) where

import Control.Monad (unless)
import qualified Data.Text.IO as TextIO
import Phil.Handoff.Phase1AssuranceInputs
  ( decodePhase1AssuranceInputs
  , derivePhase1AssuranceInputs
  , renderPhase1AssuranceInputs
  )
import Phil.Test.Phase1.ManifestWitnesses
  ( AssuranceInputFixture (..)
  , steveAssuranceInputFixture
  , uploadAssuranceInputFixture
  )
import System.Exit (die)

main :: IO ()
main = do
  regenerate "Upload"
    "handoff/phase1/witnesses/upload-assurance-inputs-v1.tsv"
    uploadAssuranceInputFixture
  regenerate "Steve"
    "handoff/phase1/witnesses/steve-assurance-inputs-v1.tsv"
    steveAssuranceInputFixture

regenerate :: String -> FilePath -> Either String AssuranceInputFixture -> IO ()
regenerate label target fixtureResult = do
  fixture <- case fixtureResult of
    Left problem -> die (label ++ " assurance fixture failed: " ++ problem)
    Right value -> pure value
  actual <- case derivePhase1AssuranceInputs
      (assuranceInputFixturePolicy fixture)
      (assuranceInputFixtureLedger fixture)
      (assuranceInputFixtureSelection fixture) of
    Left problem -> die (label ++ " assurance derivation failed: " ++ show problem)
    Right value -> pure value
  let encoded = renderPhase1AssuranceInputs actual
  decoded <- case decodePhase1AssuranceInputs encoded of
    Left problem -> die (label ++ " generated assurance input fails decoding: " ++ show problem)
    Right value -> pure value
  unless (decoded == actual) $
    die (label ++ " generated assurance input round-trip mismatch")
  TextIO.writeFile target encoded
  putStrLn ("Regenerated exact " ++ label ++ " assurance inputs: " ++ target)
