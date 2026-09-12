{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Compiler
  ( CompilerTarget
  , RunnableProgram (runnableLLVMArtifact)
  , compileRunnableForTarget
  , compilerTargetName
  , parseCompilerTarget
  , renderRunnableCompileError
  , supportedCompilerTargets
  )
import Phil.LLVM (llvmArtifactText)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (stderr)

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    ["emit-llvm", "--target", targetName, path] ->
      case parseCompilerTarget (Text.pack targetName) of
        Nothing -> do
          TextIO.hPutStrLn stderr ("unknown target: " <> Text.pack targetName)
          usage
        Just target -> emitLLVM target path
    _ -> usage

usage :: IO a
usage = do
  TextIO.hPutStrLn stderr "usage: philc emit-llvm --target TARGET FILE"
  TextIO.hPutStrLn stderr
    ("supported targets: " <> Text.intercalate ", " (map compilerTargetName supportedCompilerTargets))
  exitFailure

emitLLVM :: CompilerTarget -> FilePath -> IO ()
emitLLVM target path = do
  source <- TextIO.readFile path
  case compileRunnableForTarget target (Text.pack path) source of
    Left compileError -> do
      TextIO.hPutStrLn stderr (renderRunnableCompileError compileError)
      exitFailure
    Right runnable ->
      TextIO.putStr (llvmArtifactText (runnableLLVMArtifact runnable))
