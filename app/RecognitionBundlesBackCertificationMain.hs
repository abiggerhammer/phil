{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance.Rocq (renderRocqProofCertificate)
import Phil.Assurance.RocqBundle
import Phil.Assurance.RocqRecognitionBundles
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [checkedRoot, outputRoot] -> mapM_ (certifyOne checkedRoot outputRoot) recognitionBundleSpecs
    _ -> failWith "usage: phil-certify-recognition-bundles CHECKED_ROOT OUTPUT_ROOT"

certifyOne :: FilePath -> FilePath -> RocqProofBundleSpec -> IO ()
certifyOne checkedRoot outputRoot spec = do
  inputs <- mapM (readPart checkedRoot) (rocqBundleParts spec)
  case certifyRocqProofBundle spec inputs of
    Left err ->
      failWith
        ("Recognition proof-bundle back-certification failed for " <>
          Text.unpack (unObligationId (rocqBundleObligation spec)) <> ": " <> show err)
    Right result -> do
      putStrLn
        ("certified bundle " <>
          Text.unpack (unObligationId (rocqBundleObligation spec)) <>
          " revision " <>
          Text.unpack (unRevisionId (revisionId (rocqBundleResultRevision result))))
      mapM_ (writePart outputRoot spec) (rocqBundleResultParts result)

readPart
  :: FilePath
  -> RocqProofPartSpec
  -> IO (ByteString.ByteString, ByteString.ByteString)
readPart checkedRoot part = do
  sourceBytes <- ByteString.readFile
    (checkedRoot </> Text.unpack (unArtifactRef (rocqPartSourceRef part)))
  compiledBytes <- ByteString.readFile
    (checkedRoot </> Text.unpack (unArtifactRef (rocqPartCompiledRef part)))
  pure (sourceBytes, compiledBytes)

writePart :: FilePath -> RocqProofBundleSpec -> RocqProofPartResult -> IO ()
writePart outputRoot spec result = do
  let part = rocqPartResultSpec result
      obligation = unObligationId (rocqBundleObligation spec)
      role = unEvidenceRole (rocqPartRole part)
      outputPath = outputRoot </>
        Text.unpack obligation <> "." <> Text.unpack role <> ".rocq.cert"
      certificate = rocqPartResultCertificate result
      artifact = rocqPartResultCertificateArtifact result
  ByteString.writeFile outputPath
    (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
  putStrLn
    ("  " <> Text.unpack role <> " certificate sha256: " <>
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
