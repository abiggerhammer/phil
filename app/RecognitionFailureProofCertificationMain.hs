{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Systems.RecognitionFailureProofCertification
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  let root = "rocq-recognition-failure" </> "proof" </> "Phil" </> "Systems"
      output = "recognition-failure-certificates"
      sourcePath = root </> "RecognitionFailureDetail.v"
      objectPath = root </> "RecognitionFailureDetail.vo"
      outputPath = output </> "PHIL-SYS-RECOG-FAIL-DETAIL-001.rocq.cert"
  sourceBytes <- ByteString.readFile sourcePath
  objectBytes <- ByteString.readFile objectPath
  case certifyRocqProof systemsRecognitionFailureDetailCertificationSpec sourceBytes objectBytes of
    Left err -> failWith ("Recognition Failure Detail Rocq certification failed: " <> show err)
    Right bundle -> do
      let certificate = rocqBundleCertificate bundle
          artifact = rocqBundleCertificateArtifact bundle
      ByteString.writeFile outputPath
        (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
      putStrLn "certified PHIL-SYS-RECOG-FAIL-DETAIL-001"
      putStrLn ("certificate artifact: " <>
        Text.unpack (unArtifactRef (artifactReference artifact)))
      putStrLn ("certificate sha256: " <>
        Text.unpack (unDigest (artifactDigest artifact)))

(</>) :: FilePath -> FilePath -> FilePath
left </> right
  | null left = right
  | last left == '/' = left <> right
  | otherwise = left <> "/" <> right

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr message
  exitFailure
