{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Compiler
  ( RunnableProgram (runnableLLVMArtifact)
  , compileRunnable
  , renderRunnableCompileError
  )
import Phil.LLVM (llvmArtifactText)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (stderr)

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    ["emit-llvm", path] -> emitLLVM path
    _ -> do
      TextIO.hPutStrLn stderr "usage: philc emit-llvm FILE"
      exitFailure

emitLLVM :: FilePath -> IO ()
emitLLVM path = do
  source <- TextIO.readFile path
  case compileRunnable (Text.pack path) source of
    Left compileError -> do
      TextIO.hPutStrLn stderr (renderRunnableCompileError compileError)
      exitFailure
    Right runnable ->
      TextIO.putStr (llvmArtifactText (runnableLLVMArtifact runnable))
