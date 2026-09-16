{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance.Rocq
import Phil.Assurance.RocqCoreControlAssurance
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [checkedRoot, outputRoot] ->
      mapM_ (certifyOne checkedRoot outputRoot) coreControlAssuranceCertificationSpecs
    _ -> failWith "usage: phil-certify-core-control-assurance CHECKED_ROOT OUTPUT_ROOT"

certifyOne :: FilePath -> FilePath -> RocqCertificationSpec -> IO ()
certifyOne checkedRoot outputRoot spec = do
  let sourcePath = checkedRoot </> Text.unpack (unArtifactRef (rocqSpecSourceRef spec))
      objectPath = checkedRoot </> Text.unpack (unArtifactRef (rocqSpecCompiledRef spec))
      obligation = unObligationId (rocqSpecObligation spec)
      outputPath = outputRoot </> Text.unpack obligation <> ".rocq.cert"
  sourceBytes <- ByteString.readFile sourcePath
  objectBytes <- ByteString.readFile objectPath
  case packageTrustedRocqProof spec sourceBytes objectBytes of
    Left err ->
      failWith
        ("Core control/assurance back-certification failed for " <>
          Text.unpack obligation <> ": " <> show err)
    Right bundle -> do
      let certificate = rocqBundleCertificate bundle
          artifact = rocqBundleCertificateArtifact bundle
      ByteString.writeFile outputPath
        (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
      putStrLn ("certified " <> Text.unpack obligation)
      putStrLn
        ("certificate sha256: " <>
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
