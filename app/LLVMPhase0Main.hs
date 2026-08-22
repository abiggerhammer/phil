module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.LLVM (llvmArtifactText, phase0LLVMArtifact)

main :: IO ()
main = TextIO.putStr (llvmArtifactText phase0LLVMArtifact)
