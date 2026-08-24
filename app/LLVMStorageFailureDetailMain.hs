module Main (main) where

import qualified Data.Text.IO as Text
import Phil.LLVM (llvmArtifactText, phase0StorageFailureDetailLLVMArtifact)

main :: IO ()
main = case phase0StorageFailureDetailLLVMArtifact of
  Left err -> fail (show err)
  Right artifact -> Text.putStr (llvmArtifactText artifact)
