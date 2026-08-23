module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( finalResponseReceiveCertificationLLVM
  , llvmArtifactText
  , phase0FinalResponseReceiveLLVMCertification
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO () = case phase0FinalResponseReceiveLLVMCertification of
  Left verificationError -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 final-response receive LLVM certification failed: " <> show verificationError
    exitFailure
  Right bundle ->
    TextIO.putStr (llvmArtifactText (finalResponseReceiveCertificationLLVM bundle))
