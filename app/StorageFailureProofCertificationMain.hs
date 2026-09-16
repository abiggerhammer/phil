{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Systems.StorageFailureProofCertification
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  let root = "rocq-storage-failure-detail" </> "proof" </> "Phil" </> "Systems"
      output = "storage-failure-detail-certificates"
      sourcePath = root </> "StorageFailureDetail.v"
      objectPath = root </> "StorageFailureDetail.vo"
      outputPath = output </> "PHIL-SYS-STORAGE-FAIL-DETAIL-001.rocq.cert"
  sourceBytes <- ByteString.readFile sourcePath
  objectBytes <- ByteString.readFile objectPath
  case packageTrustedRocqProof systemsStorageFailureDetailCertificationSpec sourceBytes objectBytes of
    Left err -> failWith ("Storage Failure Detail Rocq certification failed: " <> show err)
    Right bundle -> do
      let certificate = rocqBundleCertificate bundle
          artifact = rocqBundleCertificateArtifact bundle
      ByteString.writeFile outputPath
        (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
      putStrLn "certified PHIL-SYS-STORAGE-FAIL-DETAIL-001"
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
