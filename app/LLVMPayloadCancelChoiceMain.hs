module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( llvmArtifactText
  , payloadCancelChoiceCertificationLLVM
  , phase0PayloadCancelChoiceLLVMCertification
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO () = case phase0PayloadCancelChoiceLLVMCertification of
  Left verificationError -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 payload/cancel choice LLVM certification failed: " <> show verificationError
    exitFailure
  Right bundle ->
    TextIO.putStr (llvmArtifactText (payloadCancelChoiceCertificationLLVM bundle))
