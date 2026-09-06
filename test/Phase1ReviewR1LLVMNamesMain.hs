{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler
  ( RunnableProgram (..)
  , compileRunnable
  )
import Phil.LLVM.IR (LLVMArtifact (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "R1 source and synthetic scalar names remain distinct after LLVM rendering" sourceSyntheticCollision
    , test "R1 source scalar and entry block names occupy distinct LLVM namespaces" valueBlockCollision
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

sourceSyntheticCollision :: Either String ()
sourceSyntheticCollision = do
  rendered <- compileText $ Text.unlines
    [ "component main provides U32 {"
    , "  let return_value_0 = 1"
    , "  return 2"
    , "}"
    ]
  assertContains "%source_value_return_value_0 = add i32 0, 1" rendered
  assertContains "%synthetic_return_value_0 = add i32 0, 2" rendered
  assert (countOccurrences "%source_value_return_value_0 =" rendered == 1)
    "source scalar definition was not unique"
  assert (countOccurrences "%synthetic_return_value_0 =" rendered == 1)
    "synthetic return definition was not unique"

valueBlockCollision :: Either String ()
valueBlockCollision = do
  rendered <- compileText $ Text.unlines
    [ "component main provides U32 {"
    , "  let entry = 42"
    , "  return entry"
    , "}"
    ]
  assertContains "block_entry:" rendered
  assertContains "%source_value_entry = add i32 0, 42" rendered
  assert (not (Text.isInfixOf "\nentry:\n" rendered))
    "raw source spelling still occupied the LLVM block-label namespace"

compileText :: Text -> Either String Text
compileText source =
  case compileRunnable "review-r1.phil" source of
    Left err -> Left ("compileRunnable rejected R1 regression source: " <> show err)
    Right runnable -> Right (llvmArtifactText (runnableLLVMArtifact runnable))

assertContains :: Text -> Text -> Either String ()
assertContains needle haystack =
  assert (Text.isInfixOf needle haystack)
    ("missing rendered LLVM fragment: " <> Text.unpack needle)

countOccurrences :: Text -> Text -> Int
countOccurrences needle = length . Text.breakOnAll needle

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail
