{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.RemainingRuntimeTestEvidenceProfiles
  ( knownRemainingRuntimeTestEvidenceCertificationSpec )
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.TestEvidenceProfiles (knownPhase0TestEvidenceCertificationSpec)
import Phil.Assurance.Types (ArtifactRef (..), unArtifactRef)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [profile, resultPath, outputPath] -> certify profile resultPath outputPath
    _ -> die "usage: phil-certify-test-evidence <profile> <result-log> <output-certificate>"

certify :: String -> FilePath -> FilePath -> IO ()
certify profile resultPath outputPath =
  case lookupSpec (Text.pack profile) of
    Nothing -> die ("unknown test-evidence certification profile: " ++ profile)
    Just spec -> do
      checkerBytes <- ByteString.readFile (artifactPath (testSpecCheckerRef spec))
      inputs <- mapM readInput (testSpecInputRefs spec)
      resultBytes <- ByteString.readFile resultPath
      case certifyTestEvidence spec checkerBytes inputs resultBytes of
        Left err -> die ("test-evidence certification failed: " ++ show err)
        Right bundle -> do
          let certificateText = renderTestEvidenceCertificate (testBundleCertificate bundle)
          TextIO.writeFile outputPath certificateText
          TextIO.putStr certificateText
          putStrLn ("certificate artifact: " ++ show (testBundleCertificateArtifact bundle))
  where
    readInput ref = do
      bytes <- ByteString.readFile (artifactPath ref)
      pure (ref, bytes)

lookupSpec :: Text.Text -> Maybe TestEvidenceCertificationSpec
lookupSpec profile =
  case knownPhase0TestEvidenceCertificationSpec profile of
    Just spec -> Just spec
    Nothing -> knownRemainingRuntimeTestEvidenceCertificationSpec profile

artifactPath :: ArtifactRef -> FilePath
artifactPath = Text.unpack . unArtifactRef
