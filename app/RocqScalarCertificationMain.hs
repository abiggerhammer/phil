{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [sourcePath, compiledPath, outputPath] -> do
      sourceBytes <- ByteString.readFile sourcePath
      compiledBytes <- ByteString.readFile compiledPath
      case certifyCoreScalarRocqProof sourceBytes compiledBytes of
        Left err -> do
          hPutStrLn stderr ("Rocq certification failed: " <> show err)
          exitFailure
        Right bundle -> do
          let certificate = rocqBundleCertificate bundle
              artifact = rocqBundleCertificateArtifact bundle
          ByteString.writeFile outputPath
            (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
          putStrLn "certified PHIL-CORE-SCALAR-001 as ProofAssistantTheorem evidence"
          putStrLn ("certificate artifact: " <> Text.unpack (unArtifactRef (artifactReference artifact)))
          putStrLn ("certificate sha256: " <> Text.unpack (unDigest (artifactDigest artifact)))
    _ -> do
      hPutStrLn stderr
        "usage: phil-certify-core-scalar SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure
