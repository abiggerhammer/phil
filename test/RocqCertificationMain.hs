{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString.Char8 as ByteString
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM
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
    , test "Systems recognized-record Rocq certificate closes its manifest"
        (certificateCloses systemsRecognizedRecordCertificationSpec)
    , test "LLVM recognized-record ABI Rocq certificate closes its manifest"
        (certificateCloses llvmRecognizedRecordABICertificationSpec)
    , test "LLVM runtime-symbol Rocq certificate closes its manifest"
        (certificateCloses llvmRuntimeSymbolCertificationSpec)
    , test "known Rocq certification profiles resolve" knownProfilesResolve
    , test "proof-bound recognized-record certification closes"
        recognizedRecordProofCertificationCloses
    , test "proof-bound certification checks proof artifact digests"
        recognizedRecordProofArtifactTamperRejects
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
knownProfilesResolve =
  all resolvesLegacy
    [ coreScalarCertificationSpec
    , systemsFieldProjectionCertificationSpec
    , llvmFieldProjectionCertificationSpec
    ]
  && all resolvesRecognizedRecord
    [ systemsRecognizedRecordCertificationSpec
    , llvmRecognizedRecordABICertificationSpec
    , llvmRuntimeSymbolCertificationSpec
    ]
  where
    resolvesLegacy spec =
      knownRocqCertificationSpec (rocqSpecProfile spec) == Just spec
    resolvesRecognizedRecord spec =
      knownRecognizedRecordRocqCertificationSpec (rocqSpecProfile spec) == Just spec

recognizedRecordProofCertificationCloses :: Bool
recognizedRecordProofCertificationCloses =
  case recognizedRecordProofCandidates of
    Just (systemsProof, abiProof, symbolProof) ->
      verifyPhase0RecognizedRecordProofCertification systemsProof abiProof symbolProof == Right ()
    Nothing -> False

recognizedRecordProofArtifactTamperRejects :: Bool
recognizedRecordProofArtifactTamperRejects =
  case recognizedRecordProofCandidates of
    Nothing -> False
    Just (systemsProof, abiProof, symbolProof) ->
      case phase0RecognizedRecordProofCertification systemsProof abiProof symbolProof of
        Left _ -> False
        Right bundle ->
          let artifact = rocqBundleCertificateArtifact systemsProof
              context0 = recognizedRecordProofCertificationContext bundle
              context = context0
                { verificationAvailableArtifacts = Map.insert
                    (artifactReference artifact)
                    (digestText "tampered-proof-certificate")
                    (verificationAvailableArtifacts context0)
                }
          in case verifyManifest
              context
              (recognizedRecordProofCertificationLedger bundle)
              (recognizedRecordProofCertificationManifest bundle) of
              Left ArtifactDigestMismatch {} -> True
              _ -> False

recognizedRecordProofCandidates
  :: Maybe (RocqCertificationBundle, RocqCertificationBundle, RocqCertificationBundle)
recognizedRecordProofCandidates = do
  systemsProof <- either (const Nothing) Just
    (candidate systemsRecognizedRecordCertificationSpec "systems-compiled")
  abiProof <- either (const Nothing) Just
    (candidate llvmRecognizedRecordABICertificationSpec "abi-compiled")
  symbolProof <- either (const Nothing) Just
    (candidate llvmRuntimeSymbolCertificationSpec "symbol-compiled")
  pure (systemsProof, abiProof, symbolProof)

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
