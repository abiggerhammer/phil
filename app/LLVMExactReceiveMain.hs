module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( llvmArtifactText
  , phase0ExactReceiveLLVMArtifact
  , verifyPhase0ExactReceiveLLVM
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO () = case verifyPhase0ExactReceiveLLVM of
  Left verificationError -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 transport exact-receive LLVM verification failed: " <> show verificationError
    exitFailure
  Right () -> case phase0ExactReceiveLLVMArtifact of
    Left systemsError -> do
      IO.hPutStrLn IO.stderr $
        "Phase 0 transport exact-receive Systems candidate failed: " <> show systemsError
      exitFailure
    Right artifact -> TextIO.putStr (llvmArtifactText artifact)
