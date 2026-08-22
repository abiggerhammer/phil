{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text.IO as Text
import Phil.LLVM
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = case phase0RecognizedRecordLLVMArtifact of
  Left err -> do
    hPutStrLn stderr ("recognized-record LLVM candidate failed verification: " <> show err)
    exitFailure
  Right artifact -> Text.putStr (llvmArtifactText artifact)
