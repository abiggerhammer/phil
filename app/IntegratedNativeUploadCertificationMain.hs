{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance.IntegratedNativeUploadTestEvidence
import Phil.Assurance.Phase0ClosureCertification
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.Types
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  let output = "phase0-integrated-native-certificates"
      checkerPath = "runtime/phase0/integrated_upload_v1_main.c"
      resultPath = "phase0-integrated-native-evidence.log"
      runtimeCertPath = output </> "PHIL-RUNTIME-INTEGRATED-UPLOAD-001.test.cert"
      closureCertPath = output </> "PHIL-PHASE0-CERT-001.cert"

  checkerBytes <- ByteString.readFile checkerPath
  inputs <- mapM readInput integratedNativeUploadInputPaths
  resultBytes <- ByteString.readFile resultPath

  runtimeBundle <- case certifyTestEvidence
      integratedNativeUploadCertificationSpec
      checkerBytes
      inputs
      resultBytes of
    Left err -> failWith ("Integrated native upload test certification failed: " <> show err)
    Right bundle -> pure bundle

  let runtimeCertificate = testBundleCertificate runtimeBundle
      runtimeArtifact = testBundleCertificateArtifact runtimeBundle
  ByteString.writeFile runtimeCertPath
    (TextEncoding.encodeUtf8 (renderTestEvidenceCertificate runtimeCertificate))

  closureBundle <- case phase0ClosureCertification runtimeBundle of
    Left err -> failWith ("Phase 0 closure certification failed: " <> show err)
    Right bundle -> pure bundle

  let closureArtifact = phase0ClosureArtifact closureBundle
  ByteString.writeFile closureCertPath
    (TextEncoding.encodeUtf8 (renderPhase0ClosureCertification closureBundle))

  putStrLn "certified PHIL-RUNTIME-INTEGRATED-UPLOAD-001"
  printArtifact runtimeArtifact
  putStrLn "certified PHIL-PHASE0-CERT-001"
  printArtifact closureArtifact

readInput :: Text.Text -> IO (ArtifactRef, ByteString.ByteString)
readInput path = do
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
