{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.RocqBundle
import Phil.Assurance.RocqRecognitionBundles
import Phil.Assurance.Types
import Phil.Assurance.Verify
import Phil.Core.Syntax (ObligationId (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [checkedRoot] -> do
      results <- mapM (checkBundle checkedRoot) recognitionBundleSpecs
      if and results then pure () else exitFailure
    _ -> failWith "usage: phil-check-recognition-bundles CHECKED_ROOT"

checkBundle :: FilePath -> RocqProofBundleSpec -> IO Bool
checkBundle checkedRoot spec = do
  inputs <- mapM (readPart checkedRoot) (rocqBundleParts spec)
  case certifyRocqProofBundle spec inputs of
    Left err -> do
      hPutStrLn stderr ("bundle unexpectedly rejected: " <> show err)
      pure False
    Right result -> do
      missingChecks <- mapM (missingPartRejects result)
        (rocqBundleResultParts result)
      let duplicateRoleCheck = duplicateRoleRejects spec inputs
          ok = and missingChecks && duplicateRoleCheck
      putStrLn
        ((if ok then "PASS: " else "FAIL: ") <>
          Text.unpack (unObligationId (rocqBundleObligation spec)) <>
          " requires every distinct proof-part role")
      pure ok

missingPartRejects :: RocqProofBundleResult -> RocqProofPartResult -> IO Bool
missingPartRejects result partResult = do
  let part = rocqPartResultSpec partResult
      evidenceId = rocqPartEvidenceId part
      ledger = rocqBundleResultLedger result
      originalManifest = rocqBundleResultManifest result
      provisional = originalManifest
        { manifestEvidenceEntries =
            Set.delete evidenceId (manifestEvidenceEntries originalManifest)
        }
      weakened = provisional
        { manifestId = deriveManifestId ledger provisional }
      context = rocqBundleResultVerificationContext result
      revision = revisionId (rocqBundleResultRevision result)
  pure $ case verifyManifest context ledger weakened of
    Left (AcceptanceRuleUnsatisfied actual) -> actual == revision
    _ -> False

duplicateRoleRejects
  :: RocqProofBundleSpec
  -> [(ByteString.ByteString, ByteString.ByteString)]
  -> Bool
duplicateRoleRejects spec inputs =
  case rocqBundleParts spec of
    firstPart : secondPart : rest ->
      let duplicate = secondPart { rocqPartRole = rocqPartRole firstPart }
          badSpec = spec { rocqBundleParts = firstPart : duplicate : rest }
      in case certifyRocqProofBundle badSpec inputs of
          Left (RocqBundleDuplicateRole role) -> role == rocqPartRole firstPart
          _ -> False
    _ -> False

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

(</>) :: FilePath -> FilePath -> FilePath
left </> right
  | null left = right
  | last left == '/' = left <> right
  | otherwise = left <> "/" <> right

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr message
  exitFailure
