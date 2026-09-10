{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM.IR (LLVMArtifact (..))
import Phil.Test.Phase1.CertifiedReleaseWitnesses
import Phil.Test.Phase1.ManifestWitnesses
import Phil.Verification.CertifiedRelease
  ( CertifiedReleaseArtifact
  , certifiedReleaseLLVMArtifact
  )
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["upload"] -> do
      clientSource <- TextIO.readFile "examples/upload/client.phil"
      serverSource <- TextIO.readFile "examples/upload/server.phil"
      emitCertified "Upload" (uploadRealManifestFixture clientSource serverSource)
    ["steve"] -> do
      putSource <- TextIO.readFile "examples/steve/put.phil"
      getSource <- TextIO.readFile "examples/steve/get.phil"
      emitCertified "Steve" (steveRealManifestFixture putSource getSource)
    _ -> do
      hPutStrLn stderr "usage: Phase1INT005EmitCertifiedReleaseMain.hs <upload|steve>"
      exitFailure

emitCertified :: String -> Either String RealManifestFixture -> IO ()
emitCertified label fixtureResult = case fixtureResult of
  Left detail -> failWith (label <> " real manifest fixture failed: " <> detail)
  Right fixture -> case certifyConventionalFixture fixture of
    Left detail -> failWith (label <> " certified release failed: " <> show detail)
    Right certified -> emitLLVM certified

emitLLVM :: CertifiedReleaseArtifact -> IO ()
emitLLVM = TextIO.putStr
  . llvmArtifactText
  . certifiedReleaseLLVMArtifact

failWith :: String -> IO a
failWith detail = hPutStrLn stderr detail >> exitFailure
