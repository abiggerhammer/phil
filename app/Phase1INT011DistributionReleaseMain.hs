{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Types (Digest)
import Phil.Handoff.Phase1Manifest (sha256File)
import Phil.Verification.DistributionRelease
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (takeFileName)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["emit-linux", packageName, version, sourceCommit, handoffPath, compilerPath] ->
      emitRelease
        (Text.pack packageName)
        (Text.pack version)
        "x86_64-unknown-linux-gnu"
        (Text.pack sourceCommit)
        handoffPath
        compilerPath
        phase1LinuxDistributionTrust

    ["emit-darwin", packageName, version, sourceCommit, handoffPath, compilerPath] ->
      emitRelease
        (Text.pack packageName)
        (Text.pack version)
        "aarch64-apple-darwin"
        (Text.pack sourceCommit)
        handoffPath
        compilerPath
        phase1DarwinDistributionTrust

    ["emit-archive", releasePath, archivePath, packageManifestPath] -> do
      releaseSource <- TextIO.readFile releasePath
      releaseId <- case parseRenderedDistributionReleaseId releaseSource of
        Left errorValue -> failWith (show errorValue)
        Right value -> pure value
      archiveDigest <- requireFileDigest archivePath
      packageManifestDigest <- requireFileDigest packageManifestPath
      binding <- case buildPhase1DistributionArchive
          releaseId
          (Text.pack (takeFileName archivePath))
          archiveDigest
          packageManifestDigest of
        Left errorValue -> failWith (show errorValue)
        Right value -> pure value
      TextIO.putStr (renderPhase1DistributionArchive binding)

    _ -> do
      hPutStrLn stderr
        "usage: Phase1INT011DistributionReleaseMain.hs emit-linux|emit-darwin PACKAGE VERSION SOURCE_COMMIT HANDOFF_PATH COMPILER_PATH"
      hPutStrLn stderr
        "   or: Phase1INT011DistributionReleaseMain.hs emit-archive RELEASE_PATH ARCHIVE_PATH PACKAGE_MANIFEST_PATH"
      exitFailure

emitRelease
  :: Text
  -> Text
  -> Text
  -> Text
  -> FilePath
  -> FilePath
  -> [DistributionTrustBoundary]
  -> IO ()
emitRelease packageName version target sourceCommit handoffPath compilerPath trust = do
  handoff <- requireFileDigest handoffPath
  compiler <- requireFileDigest compilerPath
  release <- case buildPhase1DistributionRelease
      packageName
      version
      target
      sourceCommit
      handoff
      compiler
      trust of
    Left errorValue -> failWith (show errorValue)
    Right value -> pure value
  TextIO.putStr (renderPhase1DistributionRelease release)

requireFileDigest :: FilePath -> IO Digest
requireFileDigest path = do
  result <- sha256File path
  case result of
    Left detail -> failWith (path <> ": " <> Text.unpack detail)
    Right raw -> case parseSha256Digest raw of
      Left errorValue -> failWith (show errorValue)
      Right digest -> pure digest

failWith :: String -> IO a
failWith detail = hPutStrLn stderr detail >> exitFailure
