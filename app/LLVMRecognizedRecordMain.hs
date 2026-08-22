module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( llvmArtifactText
  , phase0RecognizedRecordLLVMArtifact
  , verifyPhase0RecognizedRecordLLVM
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO ()
main = case verifyPhase0RecognizedRecordLLVM of
  Left verificationError -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 recognized-record LLVM verification failed: " <> show verificationError
    exitFailure
  Right () -> case phase0RecognizedRecordLLVMArtifact of
    Left systemsError -> do
      IO.hPutStrLn IO.stderr $
        "Phase 0 recognized-record Systems candidate failed: " <> show systemsError
      exitFailure
    Right artifact -> TextIO.putStr (llvmArtifactText artifact)
