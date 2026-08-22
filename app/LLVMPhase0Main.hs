module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM.Phase0 (phase0LLVMArtifact)
import Phil.LLVM.IR (llvmArtifactText)

main :: IO ()
main = TextIO.putStr (llvmArtifactText phase0LLVMArtifact)
