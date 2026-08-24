{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.LLVM
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "control codec translation verifies" candidateVerifies
    , test "control codec profile is exact" profileExact
    , test "wire descriptor fixes canonical Hello and Begin framing" descriptorExact
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = verifyPhase0ControlCodecLLVM == Right ()

profileExact :: Bool
profileExact = case phase0ControlCodecLLVMArtifact of
  Left _ -> False
  Right artifact ->
    llvmRuntimeABIProfile (llvmArtifactModule artifact)
      == "phil-runtime/phase0/control-codec-v1"
      && Text.isInfixOf
          "; runtime-abi-profile=phil-runtime/phase0/control-codec-v1"
          (llvmArtifactText artifact)

descriptorExact :: Bool
descriptorExact = all (`Text.isInfixOf` controlCodecABIDescriptor)
  [ "frame.magic=50:48:49:4c"
  , "frame.codec-version=01"
  , "frame.tag.Hello=01"
  , "frame.tag.Begin=02"
  , "hello.canonical=strictly-increasing-versions"
  , "begin.digest-alg.sha256=01"
  , "integer-byte-order=big-endian"
  , "codec-provider=single-shared-client-encoder/server-decoder-implementation"
  ]

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
