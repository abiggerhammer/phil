module Main (main) where

import qualified Data.Text.IO as Text
import Phil.LLVM (llvmArtifactText, phase0VersionSessionChoiceLLVMArtifact)

main :: IO ()
main =
  case phase0VersionSessionChoiceLLVMArtifact of
    Left err -> fail (show err)
    Right artifact -> Text.putStr (llvmArtifactText artifact)
