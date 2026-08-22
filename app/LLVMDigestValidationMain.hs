module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( llvmArtifactText
  , phase0DigestValidationLLVMArtifact
  , verifyPhase0DigestValidationLLVM
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO ()
main = case verifyPhase0DigestValidationLLVM of
  Left verificationError -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 digest-validation LLVM verification failed: " <> show verificationError
    exitFailure
  Right () -> case phase0DigestValidationLLVMArtifact of
    Left systemsError -> do
      IO.hPutStrLn IO.stderr $
        "Phase 0 digest-validation Systems candidate failed: " <> show systemsError
      exitFailure
    Right artifact -> TextIO.putStr (llvmArtifactText artifact)
