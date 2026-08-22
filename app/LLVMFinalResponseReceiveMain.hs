module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( llvmArtifactText
  , phase0FinalResponseReceiveLLVMArtifact
  , verifyPhase0FinalResponseReceiveLLVM
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO () = case (verifyPhase0FinalResponseReceiveLLVM, phase0FinalResponseReceiveLLVMArtifact) of
  (Left verificationError, _) -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 final-response receive LLVM verification failed: " <> show verificationError
    exitFailure
  (_, Left systemsError) -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 final-response Systems candidate failed: " <> show systemsError
    exitFailure
  (Right (), Right artifact) -> TextIO.putStr (llvmArtifactText artifact)
