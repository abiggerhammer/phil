{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance.Rocq
import Phil.Assurance.RocqValidityScope
import Phil.Assurance.Types
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [sourcePath, objectPath, outputPath] -> do
      sourceBytes <- ByteString.readFile sourcePath
      objectBytes <- ByteString.readFile objectPath
      case packageTrustedRocqProof validityScopeCertificationSpec sourceBytes objectBytes of
        Left err -> failWith ("validity-scope proof certification failed: " <> show err)
        Right bundle -> do
          let certificate = rocqBundleCertificate bundle
              artifact = rocqBundleCertificateArtifact bundle
          ByteString.writeFile outputPath
            (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
          putStrLn "certified PHIL-ASSURE-VALIDITY-001"
          putStrLn
            ("certificate artifact: " <>
              Text.unpack (unArtifactRef (artifactReference artifact)))
          putStrLn
            ("certificate sha256: " <>
              Text.unpack (unDigest (artifactDigest artifact)))
    _ -> failWith
      "usage: phil-certify-validity-scope SOURCE.v SOURCE.vo OUTPUT.cert"

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr message
  exitFailure
