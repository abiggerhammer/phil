module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( llvmArtifactText
  , phase0RejectedResponseLLVMCertification
  , rejectedResponseCertificationLLVM
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO ()
main = case phase0RejectedResponseLLVMCertification of
  Left verificationError -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 rejected-response LLVM certification failed: " <> show verificationError
    exitFailure
  Right bundle ->
    TextIO.putStr (llvmArtifactText (rejectedResponseCertificationLLVM bundle))
