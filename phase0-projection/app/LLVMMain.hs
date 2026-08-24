{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance (unDigest)
import Phil.LLVM
  ( LLVMVerificationContext (..)
  , llvmArtifactText
  , lowerSystemsControlCodec
  , phase0ControlCodecLLVMTarget
  , phase0ControlCodecLLVMVerificationContext
  , verifyLLVMEmissionWith
  )
import Phil.Phase0UploadProjection
import Phil.Systems
  ( phase0StorageFailureBundle
  , storageFailureContext
  )
import System.Directory (doesFileExist)

main :: IO ()
main = do
  clientPath <- findFixture "examples/upload/client.phil"
  serverPath <- findFixture "examples/upload/server.phil"
  clientSource <- TextIO.readFile clientPath
  serverSource <- TextIO.readFile serverPath
  projection <- either (fail . show) pure
    (projectPhase0UploadSources clientSource serverSource)
  baseline <- either (fail . show) pure phase0StorageFailureBundle
  let systemsArtifact = phase0ProjectionFinalArtifact projection
      systemsContext = phase0ProjectionFinalContext projection
      llvmArtifact = lowerSystemsControlCodec
        phase0ControlCodecLLVMTarget systemsArtifact
      llvmContext =
        (phase0ControlCodecLLVMVerificationContext baseline)
          { llvmSystemsContext = systemsContext }
  either (fail . show) pure
    (verifyLLVMEmissionWith
      lowerSystemsControlCodec
      llvmContext
      systemsArtifact
      llvmArtifact)
  TextIO.putStrLn
    ("; phase0-source-pair-digest="
      <> unDigest (phase0ProjectionSourceDigest projection))
  TextIO.putStrLn "; phase0-source-projection=surface-to-systems/phase0-upload/v1"
  TextIO.putStr (llvmArtifactText llvmArtifact)

findFixture :: FilePath -> IO FilePath
findFixture relative = do
  let candidates = [relative, "../" <> relative]
  existing <- filterM doesFileExist candidates
  case existing of
    path : _ -> pure path
    [] -> fail ("could not locate Phase 0 fixture " <> relative)

filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
filterM _ [] = pure []
filterM predicate (value : rest) = do
  keep <- predicate value
  remaining <- filterM predicate rest
  pure (if keep then value : remaining else remaining)
