{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString.Char8 as ByteString
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "core scalar Rocq certificate closes its manifest" certificateCloses
    , test "missing expected theorem rejects certification" missingTheoremRejects
    , test "compiled proof object is content-bound" compiledObjectIsBound
    , test "certificate artifact digest is checked by the manifest" certificateTamperRejects
    ]
  if and results then pure () else exitFailure

certificateCloses :: Bool
certificateCloses = case candidate "compiled-one" of
  Left _ -> False
  Right bundle ->
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle) == Right ()

missingTheoremRejects :: Bool
missingTheoremRejects =
  case certifyCoreScalarRocqProof
      (ByteString.pack (Text.unpack sourceWithoutLastTheorem))
      (ByteString.pack "compiled") of
    Left (RocqExpectedTheoremMissing "uint_at_modulus_is_invalid") -> True
    _ -> False

compiledObjectIsBound :: Bool
compiledObjectIsBound = case (candidate "compiled-one", candidate "compiled-two") of
  (Right first, Right second) ->
    artifactDigest (rocqBundleCertificateArtifact first)
      /= artifactDigest (rocqBundleCertificateArtifact second)
  _ -> False

certificateTamperRejects :: Bool
certificateTamperRejects = case candidate "compiled-one" of
  Left _ -> False
  Right bundle ->
    let artifact = rocqBundleCertificateArtifact bundle
        context = (rocqBundleVerificationContext bundle)
          { verificationAvailableArtifacts = Map.singleton
              (artifactReference artifact)
              (digestText "tampered")
          }
    in case verifyManifest context (rocqBundleLedger bundle) (rocqBundleManifest bundle) of
        Left ArtifactDigestMismatch {} -> True
        _ -> False

candidate :: String -> Either RocqCertificationError RocqCertificationBundle
candidate compiled = certifyCoreScalarRocqProof
  (ByteString.pack (Text.unpack validSource))
  (ByteString.pack compiled)

validSource :: Text
validSource = Text.unlines
  ("(* PHIL-CORE-SCALAR-001 *)" : map ("Theorem " <>) coreScalarTheorems)

sourceWithoutLastTheorem :: Text
sourceWithoutLastTheorem = Text.unlines
  ("(* PHIL-CORE-SCALAR-001 *)" : map ("Theorem " <>) (init coreScalarTheorems))

test :: String -> Bool -> IO Bool
test label result = do
  putStrLn ((if result then "PASS " else "FAIL ") <> label)
  pure result
