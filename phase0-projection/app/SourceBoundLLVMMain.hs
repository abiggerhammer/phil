{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
import Phil.Phase0UploadProjection
import Phil.Systems
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  clientSource <- TextIO.readFile "examples/upload/client.phil"
  serverSource <- TextIO.readFile "examples/upload/server.phil"
  case projectPhase0UploadSources clientSource serverSource of
    Left err -> failWith ("projection failed: " <> show err)
    Right projection -> case phase0StorageFailureBundle of
      Left err -> failWith ("baseline StorageFailure bundle failed: " <> show err)
      Right baseline -> do
        let finalArtifact = phase0ProjectionFinalArtifact projection
            llvmArtifact = lowerSystemsControlCodec phase0ControlCodecLLVMTarget finalArtifact
            llvmContext =
              (phase0ControlCodecLLVMVerificationContext baseline)
                { llvmSystemsContext = phase0ProjectionFinalContext projection }
        case verifyLLVMEmissionWith
            lowerSystemsControlCodec llvmContext finalArtifact llvmArtifact of
          Left err -> failWith ("source-bound LLVM verification failed: " <> show err)
          Right () -> TextIO.putStr (llvmArtifactText llvmArtifact)

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr message
  exitFailure
