{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text.IO as Text
import Phil.LLVM.IR (llvmArtifactText)
import Phil.LLVM.StorageCertification
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main =
  case phase0StorageLLVMCertification of
    Left err -> do
      hPutStrLn stderr ("storage LLVM certification failed: " <> show err)
      exitFailure
    Right bundle ->
      Text.putStr (llvmArtifactText (storageCertificationLLVM bundle))
