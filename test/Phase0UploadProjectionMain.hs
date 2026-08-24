{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Paths_phil_core (getDataFileName)
import Phil.Compiler.Phase0UploadProjection
import Phil.LLVM.ControlCodec
  ( lowerSystemsControlCodec
  , phase0ControlCodecLLVMTarget
  , phase0ControlCodecLLVMVerificationContext
  )
import Phil.LLVM.IR (llvmArtifactModule, llvmRuntimeABIProfile)
import Phil.LLVM.Verify
  ( LLVMVerificationContext (..)
  , verifyLLVMEmissionWith
  )
import Phil.Systems.IR
import Phil.Systems.StorageFailure (phase0StorageFailureBundle)
import System.Exit (exitFailure)

main :: IO ()
main = do
  clientPath <- getDataFileName "examples/upload/client.phil"
  serverPath <- getDataFileName "examples/upload/server.phil"
  clientSource <- TextIO.readFile clientPath
  serverSource <- TextIO.readFile serverPath
  results <- sequence
    [ testProjection clientSource serverSource
    , testContentBinding clientSource serverSource
    , testSemanticDriftRejects clientSource serverSource
    ]
  if and results then pure () else exitFailure

testProjection :: Text.Text -> Text.Text -> IO Bool
testProjection clientSource serverSource =
  case projectPhase0UploadSources clientSource serverSource of
    Left err -> failCase ("projection failed: " <> show err)
    Right projection -> do
      let finalArtifact = phase0ProjectionFinalArtifact projection
          finalContext = phase0ProjectionFinalContext projection
          llvmArtifact = lowerSystemsControlCodec
            phase0ControlCodecLLVMTarget finalArtifact
      case phase0StorageFailureBundle of
        Left err -> failCase ("baseline storage-failure bundle failed: " <> show err)
        Right baseline -> do
          let llvmContext =
                (phase0ControlCodecLLVMVerificationContext baseline)
                  { llvmSystemsContext = finalContext }
          case verifyLLVMEmissionWith
              lowerSystemsControlCodec llvmContext finalArtifact llvmArtifact of
            Left err -> failCase ("projected codec lowering failed: " <> show err)
            Right () ->
              if llvmRuntimeABIProfile (llvmArtifactModule llvmArtifact)
                    == "phil-runtime/phase0/control-codec-v1"
                then passCase "checked source pair projects through final Systems artifact to control-codec LLVM"
                else failCase "projected codec lowering selected the wrong runtime profile"

testContentBinding :: Text.Text -> Text.Text -> IO Bool
testContentBinding clientSource serverSource =
  case ( projectPhase0UploadSources clientSource serverSource
       , projectPhase0UploadSources clientSource (serverSource <> "\n")
       ) of
    (Right original, Right whitespaceVariant) ->
      if phase0ProjectionSourceDigest original /= phase0ProjectionSourceDigest whitespaceVariant
          && systemsArtifactProgram (phase0ProjectionFinalArtifact original)
            == systemsArtifactProgram (phase0ProjectionFinalArtifact whitespaceVariant)
        then passCase "source-pair digest is content-bound while semantic projection remains stable"
        else failCase "source content binding or semantic stability check failed"
    (Left err, _) -> failCase ("original projection failed: " <> show err)
    (_, Left err) -> failCase ("whitespace-only projection failed: " <> show err)

testSemanticDriftRejects :: Text.Text -> Text.Text -> IO Bool
testSemanticDriftRejects clientSource serverSource =
  let drifted = Text.replace "record_upload_id(id)" "inspect(id)" clientSource
  in case projectPhase0UploadSources drifted serverSource of
      Left _ -> passCase "checked-but-different or invalid source semantics cannot silently reuse the upload projection"
      Right _ -> failCase "semantic source drift was silently projected to the canonical upload Systems graph"

passCase :: String -> IO Bool
passCase label = putStrLn ("PASS: " <> label) >> pure True

failCase :: String -> IO Bool
failCase detail = putStrLn ("FAIL: " <> detail) >> pure False
