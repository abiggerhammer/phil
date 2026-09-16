{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Systems.ClientOutboundProofCertification
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  let root = "rocq-client-outbound" </> "proof" </> "Phil" </> "Systems"
      output = "client-outbound-certificates"
      sourcePath = root </> "ClientOutbound.v"
      objectPath = root </> "ClientOutbound.vo"
      outputPath = output </> "PHIL-SYS-CLIENT-OUTBOUND-001.rocq.cert"
  sourceBytes <- ByteString.readFile sourcePath
  objectBytes <- ByteString.readFile objectPath
  case packageTrustedRocqProof systemsClientOutboundCertificationSpec sourceBytes objectBytes of
    Left err -> failWith ("ClientOutbound Rocq certification failed: " <> show err)
    Right bundle -> do
      let certificate = rocqBundleCertificate bundle
          artifact = rocqBundleCertificateArtifact bundle
      ByteString.writeFile outputPath
        (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
      putStrLn "certified PHIL-SYS-CLIENT-OUTBOUND-001"
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
