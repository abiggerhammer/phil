module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM
  ( llvmArtifactText
  , phase0LLVMArtifact
  , verifyPhase0LLVMCertification
  )
import System.Exit (exitFailure)
import qualified System.IO as IO

main :: IO ()
main = case verifyPhase0LLVMCertification of
  Left certificationError -> do
    IO.hPutStrLn IO.stderr $
      "Phase 0 LLVM translation certification failed: " <> show certificationError
    exitFailure
  Right () -> TextIO.putStr (llvmArtifactText phase0LLVMArtifact)
