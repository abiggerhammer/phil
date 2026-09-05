{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.ProviderQualificationIdentity
  ( ProviderQualificationAdmissionDecision (..)
  , checkedQualificationAdmissionDecision
  )
import Phil.Examples.Steve.ProviderQualifications
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "production Steve witness materializes through certified kernel"
        materializationAccepted
    , test "production DigestProvider remains admitted"
        digestAdmissionAccepted
    , test "production BlobProvider remains admitted"
        blobAdmissionAccepted
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

materializationAccepted :: Either String ()
materializationAccepted = do
  _ <- qualifications
  Right ()

digestAdmissionAccepted :: Either String ()
digestAdmissionAccepted = do
  qs <- qualifications
  assertAdmitted (steveDigestProviderQualification qs)

blobAdmissionAccepted :: Either String ()
blobAdmissionAccepted = do
  qs <- qualifications
  assertAdmitted (steveBlobProviderQualification qs)

assertAdmitted :: SteveProviderQualificationArtifact -> Either String ()
assertAdmitted artifact = case checkedQualificationAdmissionDecision
    (steveProviderCheckedAdmission artifact) of
  QualificationAdmitted -> Right ()
  QualificationRejected reasons -> Left ("qualification rejected: " <> show reasons)

qualifications :: Either String SteveProviderQualifications
qualifications = mapLeft show materializeSteveProviderQualifications

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
