{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance.ControlCodecTestEvidence
import Phil.Assurance.Rocq
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.Types
import Phil.LLVM.ControlCodecProofCertification
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  let proofRoot = "rocq-control-codec" </> "proof" </> "Phil" </> "LLVM"
      output = "control-codec-certificates"
      proofSourcePath = proofRoot </> "ControlCodec.v"
      proofObjectPath = proofRoot </> "ControlCodec.vo"
      runtimeCheckerPath = "runtime/phase0/control_codec_v1_smoke_main.c"
      runtimeResultPath = "control-codec-test-evidence.log"
      runtimeCertPath = output </> "PHIL-RUNTIME-CONTROL-CODEC-001.test.cert"
      proofCertPath = output </> "PHIL-LLVM-CONTROL-CODEC-001.rocq.cert"
      finalCertPath = output </> "PHIL-LLVM-CERT-017.proof-bound.cert"

  runtimeCheckerBytes <- ByteString.readFile runtimeCheckerPath
  runtimeInputs <- mapM readRuntimeInput controlCodecRuntimeInputPaths
  runtimeResultBytes <- ByteString.readFile runtimeResultPath

  runtimeBundle <- case certifyTestEvidence
      controlCodecRuntimeCertificationSpec
      runtimeCheckerBytes
      runtimeInputs
      runtimeResultBytes of
    Left err -> failWith ("Control Codec runtime test certification failed: " <> show err)
    Right bundle -> pure bundle

  let runtimeCertificate = testBundleCertificate runtimeBundle
      runtimeArtifact = testBundleCertificateArtifact runtimeBundle
  ByteString.writeFile runtimeCertPath
    (TextEncoding.encodeUtf8 (renderTestEvidenceCertificate runtimeCertificate))

  proofSourceBytes <- ByteString.readFile proofSourcePath
  proofObjectBytes <- ByteString.readFile proofObjectPath
  proofBundle <- case certifyRocqProof
      llvmControlCodecCertificationSpec
      proofSourceBytes
      proofObjectBytes of
    Left err -> failWith ("Control Codec Rocq certification failed: " <> show err)
    Right bundle -> pure bundle

  let proofCertificate = rocqBundleCertificate proofBundle
      proofArtifact = rocqBundleCertificateArtifact proofBundle
  ByteString.writeFile proofCertPath
    (TextEncoding.encodeUtf8 (renderRocqProofCertificate proofCertificate))

  finalBundle <- case phase0ControlCodecProofCertification proofBundle runtimeBundle of
    Left err -> failWith ("Control Codec proof-bound certification failed: " <> show err)
    Right bundle -> pure bundle

  let finalArtifact = controlCodecProofArtifact finalBundle
  ByteString.writeFile finalCertPath
    (TextEncoding.encodeUtf8 (renderControlCodecProofCertification finalBundle))

  putStrLn "certified PHIL-RUNTIME-CONTROL-CODEC-001"
  printArtifact runtimeArtifact
  putStrLn "certified PHIL-LLVM-CONTROL-CODEC-001"
  printArtifact proofArtifact
  putStrLn "certified PHIL-LLVM-CERT-017"
  printArtifact finalArtifact

readRuntimeInput :: Text.Text -> IO (ArtifactRef, ByteString.ByteString)
readRuntimeInput path = do
  bytes <- ByteString.readFile (Text.unpack path)
  pure (ArtifactRef path, bytes)

printArtifact :: ArtifactIdentity -> IO ()
printArtifact artifact = do
  putStrLn ("artifact: " <> Text.unpack (unArtifactRef (artifactReference artifact)))
  putStrLn ("sha256: " <> Text.unpack (unDigest (artifactDigest artifact)))

(</>) :: FilePath -> FilePath -> FilePath
left </> right
  | null left = right
  | last left == '/' = left <> right
  | otherwise = left <> "/" <> right

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr message
  exitFailure
