module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( acceptedResponseCertificationLLVM
  , llvmArtifactText
  , phase0AcceptedResponseLLVMCertification
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO ()
main = case phase0AcceptedResponseLLVMCertification of
  Left verificationError -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 accepted-response LLVM certification failed: " <> show verificationError
    exitFailure
  Right bundle ->
    TextIO.putStr (llvmArtifactText (acceptedResponseCertificationLLVM bundle))
