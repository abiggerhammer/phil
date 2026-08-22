{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString.Char8 as ByteString
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
import Phil.Core.Syntax (ObligationId (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "core scalar Rocq certificate closes its manifest"
        (certificateCloses coreScalarCertificationSpec)
    , test "Systems field projection Rocq certificate closes its manifest"
        (certificateCloses systemsFieldProjectionCertificationSpec)
    , test "LLVM field projection Rocq certificate closes its manifest"
        (certificateCloses llvmFieldProjectionCertificationSpec)
    , test "known Rocq certification profiles resolve" knownProfilesResolve
    , test "missing expected theorem rejects certification" missingTheoremRejects
    , test "cross-profile obligation marker rejects certification" wrongMarkerRejects
    , test "compiled proof object is content-bound" compiledObjectIsBound
    , test "certificate artifact digest is checked by the manifest" certificateTamperRejects
    ]
  if and results then pure () else exitFailure

certificateCloses :: RocqCertificationSpec -> Bool
certificateCloses spec = case candidate spec "compiled-one" of
  Left _ -> False
  Right bundle ->
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle) == Right ()

knownProfilesResolve :: Bool
knownProfilesResolve = all resolves
  [ coreScalarCertificationSpec
  , systemsFieldProjectionCertificationSpec
  , llvmFieldProjectionCertificationSpec
  ]
  where
    resolves spec =
      knownRocqCertificationSpec (rocqSpecProfile spec) == Just spec

missingTheoremRejects :: Bool
missingTheoremRejects =
  case certifyRocqProof
      coreScalarCertificationSpec
      (ByteString.pack (Text.unpack sourceWithoutLastCoreTheorem))
      (ByteString.pack "compiled") of
    Left (RocqExpectedTheoremMissing "uint_at_modulus_is_invalid") -> True
    _ -> False

wrongMarkerRejects :: Bool
wrongMarkerRejects =
  case certifyRocqProof
      systemsFieldProjectionCertificationSpec
      (ByteString.pack (Text.unpack (validSourceFor coreScalarCertificationSpec)))
      (ByteString.pack "compiled") of
    Left (RocqObligationMarkerMissing "PHIL-SYS-FIELD-PROJ-001") -> True
    _ -> False

compiledObjectIsBound :: Bool
compiledObjectIsBound = case
    ( candidate systemsFieldProjectionCertificationSpec "compiled-one"
    , candidate systemsFieldProjectionCertificationSpec "compiled-two"
    ) of
  (Right first, Right second) ->
    artifactDigest (rocqBundleCertificateArtifact first)
      /= artifactDigest (rocqBundleCertificateArtifact second)
  _ -> False

certificateTamperRejects :: Bool
certificateTamperRejects = case candidate llvmFieldProjectionCertificationSpec "compiled-one" of
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

candidate
  :: RocqCertificationSpec
  -> String
  -> Either RocqCertificationError RocqCertificationBundle
candidate spec compiled = certifyRocqProof
  spec
  (ByteString.pack (Text.unpack (validSourceFor spec)))
  (ByteString.pack compiled)

validSourceFor :: RocqCertificationSpec -> Text
validSourceFor spec = Text.unlines
  (marker : map ("Theorem " <>) (rocqSpecTheorems spec))
  where
    ObligationId obligation = rocqSpecObligation spec
    marker = "(* " <> obligation <> " *)"

sourceWithoutLastCoreTheorem :: Text
sourceWithoutLastCoreTheorem = Text.unlines
  (marker : map ("Theorem " <>) (init coreScalarTheorems))
  where
    ObligationId obligation = rocqSpecObligation coreScalarCertificationSpec
    marker = "(* " <> obligation <> " *)"

test :: String -> Bool -> IO Bool
test label result = do
  putStrLn ((if result then "PASS " else "FAIL ") <> label)
  pure result
