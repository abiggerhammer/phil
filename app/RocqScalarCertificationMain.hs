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
    [sourcePath, compiledPath, outputPath] ->
      certifyWith coreScalarCertificationSpec sourcePath compiledPath outputPath
    [profileText, sourcePath, compiledPath, outputPath] ->
      case certificationSpecFor (Text.pack profileText) of
        Nothing -> do
          hPutStrLn stderr ("unknown Rocq certification profile: " <> profileText)
          exitFailure
        Just spec -> certifyWith spec sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: phil-certify-core-scalar [PROFILE] SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

certificationSpecFor :: Text.Text -> Maybe RocqCertificationSpec
certificationSpecFor profile =
  case knownRocqCertificationSpec profile of
    Just spec -> Just spec
    Nothing -> case knownRecognizedRecordRocqCertificationSpec profile of
      Just spec -> Just spec
      Nothing -> case knownExactReceiveRocqCertificationSpec profile of
        Just spec -> Just spec
        Nothing -> knownDigestValidationRocqCertificationSpec profile

certifyWith :: RocqCertificationSpec -> FilePath -> FilePath -> FilePath -> IO ()
certifyWith spec sourcePath compiledPath outputPath = do
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
