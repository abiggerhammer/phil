module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( llvmArtifactText
  , phase0RecognizedRecordLLVMCertification
  , recognizedRecordCertificationLLVM
  , verifyPhase0RecognizedRecordLLVMCertification
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO ()
main = case verifyPhase0RecognizedRecordLLVMCertification of
  Left certificationError -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 recognized-record LLVM certification failed: " <> show certificationError
    exitFailure
  Right () -> case phase0RecognizedRecordLLVMCertification of
    Left certificationError -> do
      IO.hPutStrLn IO.stderr $
        "Phase 0 recognized-record certification construction failed: "
          <> show certificationError
      exitFailure
    Right bundle ->
      TextIO.putStr (llvmArtifactText (recognizedRecordCertificationLLVM bundle))
