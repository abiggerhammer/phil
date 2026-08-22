{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance
import Phil.Core.Syntax (ObligationId (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [profileText, sourcePath, compiledPath, outputPath] ->
      case knownRocqCertificationSpec (Text.pack profileText) of
        Nothing -> do
          hPutStrLn stderr ("unknown Rocq certification profile: " <> profileText)
          exitFailure
        Just spec -> do
          sourceBytes <- ByteString.readFile sourcePath
          compiledBytes <- ByteString.readFile compiledPath
          case certifyRocqProof spec sourceBytes compiledBytes of
            Left err -> do
              hPutStrLn stderr ("Rocq certification failed: " <> show err)
              exitFailure
            Right bundle -> do
              let certificate = rocqBundleCertificate bundle
                  artifact = rocqBundleCertificateArtifact bundle
                  ObligationId obligation = rocqCertificateObligation certificate
              ByteString.writeFile outputPath
                (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
              putStrLn
                ("certified " <> Text.unpack obligation <>
                  " as ProofAssistantTheorem evidence")
              putStrLn
                ("certificate artifact: " <>
                  Text.unpack (unArtifactRef (artifactReference artifact)))
              putStrLn
                ("certificate sha256: " <>
                  Text.unpack (unDigest (artifactDigest artifact)))
    _ -> do
      hPutStrLn stderr
        "usage: phil-certify-rocq PROFILE SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure
