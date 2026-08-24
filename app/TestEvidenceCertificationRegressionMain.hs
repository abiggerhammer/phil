{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString.Char8 as ByteString
import qualified Data.Map.Strict as Map
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.Types
import Phil.Assurance.Verify (verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  good <- expectRight "accepted exact differential evidence" $
    certifyTestEvidence syntheticSpec checkerBytes exactInputs goodResult
  missing <- expectLeft "missing required result marker rejects" $
    certifyTestEvidence syntheticSpec checkerBytes exactInputs missingMarkerResult
  forbidden <- expectLeft "forbidden result marker rejects" $
    certifyTestEvidence syntheticSpec checkerBytes exactInputs forbiddenResult
  wrongInputs <- expectLeft "wrong input identity rejects" $
    certifyTestEvidence syntheticSpec checkerBytes [(ArtifactRef "wrong-input", inputBytes)] goodResult
  scopeMismatch <- case good of
    Nothing -> pure False
    Just bundle -> do
      let badContext = (testBundleVerificationContext bundle)
            { verificationValidityContext = Map.empty }
      case verifyManifest badContext (testBundleLedger bundle) (testBundleManifest bundle) of
        Left _ -> pass "evidence validity scope remains enforced by manifest verifier"
        Right () -> failCase "evidence validity scope remains enforced by manifest verifier"
  if and [missing, forbidden, wrongInputs, scopeMismatch] && maybe False (const True) good
    then pure ()
    else exitFailure

syntheticSpec :: TestEvidenceCertificationSpec
syntheticSpec = TestEvidenceCertificationSpec
  { testSpecProfile = "synthetic"
  , testSpecObligation = ObligationId "PHIL-TEST-EVIDENCE-SYNTHETIC-001"
  , testSpecClaim = "The exact synthetic checker accepts the exact synthetic fixture."
  , testSpecKind = "Synthetic test-evidence regression"
  , testSpecOrigin = "synthetic"
  , testSpecScope = "synthetic"
  , testSpecRepresentation = "synthetic DifferentialTested evidence"
  , testSpecSubjects = ["synthetic exact result"]
  , testSpecAssuranceKind = DifferentialTested
  , testSpecCheckerRef = ArtifactRef "checker"
  , testSpecInputRefs = [ArtifactRef "input"]
  , testSpecResultRef = ArtifactRef "result"
  , testSpecCertificateRef = ArtifactRef "certificate:synthetic"
  , testSpecEvidenceId = EvidenceEntryId "evidence.synthetic"
  , testSpecExpectedMarkers = ["PASS: exact"]
  , testSpecForbiddenMarkers = ["FAIL:"]
  , testSpecValidity = ValidityScope (Map.fromList
      [ ("checker_profile", "synthetic-v1")
      , ("certificate_profile", "test-evidence-certificate/v1")
      ])
  , testSpecProducer = "synthetic producer"
  , testSpecCheckerProfile = "synthetic checker/v1"
  , testSpecResidualBoundary = "synthetic residual boundary"
  }

checkerBytes, inputBytes, goodResult, missingMarkerResult, forbiddenResult :: ByteString.ByteString
checkerBytes = ByteString.pack "checker-v1"
inputBytes = ByteString.pack "input-v1"
goodResult = ByteString.pack "PASS: exact\n"
missingMarkerResult = ByteString.pack "PASS: other\n"
forbiddenResult = ByteString.pack "PASS: exact\nFAIL: injected\n"

exactInputs :: [(ArtifactRef, ByteString.ByteString)]
exactInputs = [(ArtifactRef "input", inputBytes)]

expectRight
  :: String
  -> Either TestEvidenceCertificationError TestEvidenceCertificationBundle
  -> IO (Maybe TestEvidenceCertificationBundle)
expectRight label value = case value of
  Right bundle -> pass label >> pure (Just bundle)
  Left err -> failCase (label ++ ": " ++ show err) >> pure Nothing

expectLeft
  :: String
  -> Either TestEvidenceCertificationError TestEvidenceCertificationBundle
  -> IO Bool
expectLeft label value = case value of
  Left _ -> pass label
  Right _ -> failCase label

pass :: String -> IO Bool
pass label = putStrLn ("PASS: " ++ label) >> pure True

failCase :: String -> IO Bool
failCase label = putStrLn ("FAIL: " ++ label) >> pure False
